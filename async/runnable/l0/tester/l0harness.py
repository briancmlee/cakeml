"""
Harness for testing the L0 socket FFI (socket_ffi_l0.c).  Not trusted: it
only drives and observes.

A server CHILD process loads the shared library (its constructor runs the
startup contract) and executes ffisys_* calls on command, so its fd table
is separate from the clients'.  The parent (Server below) sends commands
over pipes moved to fds 60/61 in the child, so the child's low fds are
only 0, 1, 2 and whatever the L0 calls open.

Side commands (not FFI calls, for observation): rlimit n (RLIMIT_NOFILE),
fds (the child's open fds).
"""
import ctypes, json, os, subprocess, sys

ERR = {1: "EAGAIN", 2: "EINTR", 3: "EINPROGRESS", 4: "ECONNREFUSED", 5: "ECONNRESET",
       6: "EPIPE", 7: "ECONNABORTED", 8: "ETIMEDOUT", 9: "ENOTCONN", 10: "EMFILE",
       11: "ENFILE", 12: "ENOBUFS", 13: "ENOMEM", 14: "EADDRINUSE", 15: "EACCES",
       16: "EBADF", 17: "ENOTSOCK", 18: "EINVAL", 19: "ENETUNREACH", 20: "EHOSTUNREACH",
       21: "ENETDOWN", 22: "EPROTO", 255: "OTHER"}
HDR = 13

CHILD = r'''
import ctypes, json, os, resource, sys
r, w = int(sys.argv[2]), int(sys.argv[3])
os.dup2(r, 60); os.dup2(w, 61); os.close(r); os.close(w)
lib = ctypes.CDLL(sys.argv[1])
rd = os.fdopen(60, "r"); wr = os.fdopen(61, "w")
for line in rd:
    cmd = json.loads(line)
    if cmd[0] == "rlimit":
        resource.setrlimit(resource.RLIMIT_NOFILE, (cmd[1], resource.getrlimit(resource.RLIMIT_NOFILE)[1]))
        out = "ok"
    elif cmd[0] == "getrlimit":
        out = resource.getrlimit(resource.RLIMIT_NOFILE)[0]
    elif cmd[0] == "fds":
        out = []
        for f in range(1024):
            try:
                os.fstat(f); out.append(f)
            except OSError:
                pass
    else:
        name, conf, alen = cmd[0], bytes.fromhex(cmd[1]), cmd[2]
        c = ctypes.create_string_buffer(conf, len(conf))
        a = ctypes.create_string_buffer(alen)
        getattr(lib, "ffisys_" + name)(c, ctypes.c_long(len(conf)), a, ctypes.c_long(alen))
        out = a.raw.hex()
    wr.write(json.dumps(out) + "\n"); wr.flush()
'''

def fd8(fd):
    return fd.to_bytes(8, "big")

def decode(out):
    """The header: (code, value, errno, rest)"""
    return out[0], int.from_bytes(out[1:9], "big"), int.from_bytes(out[9:13], "big"), out[13:]

def show(res):
    code, val, e, _ = res
    return "OK %d" % val if code == 0 else "%s(errno %d, value %d)" % (ERR.get(code, code), e, val)

REV = [(1, "IN"), (2, "OUT"), (4, "ERR"), (8, "HUP"), (16, "NVAL")]

def revs(b):
    return "|".join(n for (bit, n) in REV if b & bit) or "-"

class Server:
    def __init__(self, lib):
        r1, w1 = os.pipe(); r2, w2 = os.pipe()
        self.p = subprocess.Popen([sys.executable, "-I", "-c", CHILD, lib, str(r1), str(w2)],
                                  pass_fds=(r1, w2))
        os.close(r1); os.close(w2)
        self.wr = os.fdopen(w1, "w"); self.rd = os.fdopen(r2, "r")
        self.log = []

    def raw(self, cmd):
        self.wr.write(json.dumps(cmd) + "\n"); self.wr.flush()
        line = self.rd.readline()
        if not line:
            raise RuntimeError("server child died (exit %s)" % self.p.wait())
        return json.loads(line)

    def call(self, name, conf, alen):
        out = bytes.fromhex(self.raw([name, conf.hex(), alen]))
        self.log.append(["call", name, conf.hex(), alen, out.hex()])
        return out

    def client(self, port):
        return Client(self, port)

    # The L0 calls, decoded
    def listen(self, port):
        return decode(self.call("listen", port.to_bytes(2, "big"), HDR))

    def poll(self, fds_events, block=False):
        conf = bytes([1 if block else 0]) + b"".join(fd8(f) + bytes([e]) for (f, e) in fds_events)
        res = decode(self.call("poll", conf, HDR + len(fds_events)))
        return res, list(res[3])

    def accept(self, l):
        return decode(self.call("accept", fd8(l), HDR))

    def recv(self, fd, n):
        code, val, e, rest = decode(self.call("recv", fd8(fd), HDR + n))
        return (code, val, e, rest[:val] if code == 0 else b"")

    def send(self, fd, data):
        return decode(self.call("send", fd8(fd) + data, HDR))

    def shutdown(self, fd):
        return decode(self.call("shutdown", fd8(fd), HDR))

    def close(self, fd):
        return decode(self.call("close", fd8(fd), HDR))

    def connect(self, port):
        return decode(self.call("connect", port.to_bytes(2, "big"), HDR))

    def connerr(self, fd):
        return decode(self.call("connerr", fd8(fd), HDR))

    def peer(self):
        return Peer(self)

    def rlimit(self, n):
        self.log.append(["fd_limit", n])
        return self.raw(["rlimit", n])

    def fds(self):
        return self.raw(["fds"])

    def stop(self):
        self.wr.close(); self.p.wait()

    def start_log(self):
        """The conformance log starts here: the child's open fds are the
        model's reserved fds, and its RLIMIT_NOFILE the fd limit"""
        import resource
        self.log = [["reserved", self.fds()], ["fd_limit", self.raw(["getrlimit"])]]


class Client:
    """A loopback client whose actions are logged (they are the
    environment's arrivals, delivered to the server's kernel at some
    moment the model leaves open)"""
    count = 0

    def __init__(self, server, port, connect=True):
        import socket
        self.s = server
        self.id = Client.count; Client.count += 1
        self.sock = socket.socket()
        self.sock.connect(("127.0.0.1", port))
        self.s.log.append(["connect", self.id, port])

    def send(self, data):
        self.sock.sendall(data); self.s.log.append(["data", self.id, data.hex()])

    def shutdown(self):
        import socket
        self.sock.shutdown(socket.SHUT_WR); self.s.log.append(["eof", self.id])

    def close(self):
        self.sock.close(); self.s.log.append(["close", self.id])

    def rst(self):
        import socket, struct
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
        self.sock.close(); self.s.log.append(["rst", self.id])

    def recv(self, n, timeout=0.2):
        """What the client got; ("err", errno) on an error"""
        import socket
        self.sock.settimeout(timeout)
        try:
            d = self.sock.recv(n)
            self.s.log.append(["drain", self.id, len(d)])
            return d
        except socket.timeout:
            return None
        except OSError as e:
            self.s.log.append(["client_err", self.id, e.errno])
            return ("err", e.errno)


class Peer:
    """A loopback listener the program connects to (sys_connect).  Each
    connection it accepts is the far end of one program connect; its
    actions are the environment's arrivals for that channel, logged as a
    client's, after a "link" event naming the connect (0, 1, ... in the
    order of the program's connects that made a socket)"""

    def __init__(self, server):
        import socket
        self.s = server
        self.lsock = socket.socket()
        self.lsock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.lsock.bind(("127.0.0.1", 0)); self.lsock.listen(16)
        self.port = self.lsock.getsockname()[1]

    def accept(self, k, timeout=1.0):
        """Accept the far end of the program's k-th connect"""
        self.lsock.settimeout(timeout)
        sock, _ = self.lsock.accept()
        return PeerConn(self.s, sock, k)

    def close(self):
        self.lsock.close()


class PeerConn(Client):
    def __init__(self, server, sock, k):
        self.s = server
        self.id = Client.count; Client.count += 1
        self.sock = sock
        self.s.log.append(["link", self.id, k])
