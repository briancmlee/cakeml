#!/usr/bin/env python3
"""
Model-based tester for the trusted C socket layer (async/runnable/socket_ffi.c)
against the version-2 HOL socket model (async/socket-v2/socketV2FFIScript.sml).

Not trusted: it only drives and observes.  Design (async/design/29-ffi-model-test.md):

  - A server child process loads socket_ffi.c as a shared library (its
    constructor creates the listener, fd 3) and executes ffisock_* calls on
    command, returning the output buffer.  It only runs the five FFI calls
    (plus a side query: the peer port of an fd, to identify clients).
  - The parent drives real loopback clients (connect, send, shutdown(SHUT_WR),
    receive) and the server's calls, at random, and steps a faithful Python
    transcription of the model alongside (ModelV2 below).
  - Each call's (name, conf, bytes-in, bytes-out) is compared with the
    model's ffi_sock_*2 on the same inputs; each client's received bytes are
    compared with the model's outgoing log.  Every step is logged (JSON) so
    that hol_check.py can EVALuate the HOL model on it.

Time: the model's schedule delivers one step of arrivals at each sock_poll.
The tester performs the client actions of a step just before the poll that
delivers them, then waits SETTLE seconds so the kernel has them.
"""
import ctypes, json, os, random, socket, subprocess, sys, time, fcntl, select

HERE = os.path.dirname(os.path.abspath(__file__))
FFI_C = os.path.join(HERE, "..", "runnable", "socket_ffi.c")
LIB = os.path.join(HERE, "build", "libsocket_ffi.dylib")
SETTLE = 0.01

# ---------------------------------------------------------------------------
# Byte encodings (ffiSpikeSocketFFI: fd_bytes / bytes_fd, n2w8)

def fd_bytes(fd):
    return fd.to_bytes(8, "big")

def bytes_fd(b):
    return int.from_bytes(b[:8], "big")

def fds_bytes(fds):
    return b"".join(fd_bytes(f) for f in fds)

def bytes_fds(b):
    return [bytes_fd(b[i:i + 8]) for i in range(0, len(b) - len(b) % 8, 8)]

# ---------------------------------------------------------------------------
# The model, transcribed from socketV2FFIScript.sml (version 2: clients,
# lowest free fd, close).  Lists are kept in the HOL order (open_fds is
# consed onto, ADELKEY filters), so a state can be printed as a HOL term.

class Conn:
    def __init__(self):
        self.incoming = b""
        self.peer_closed = False
        self.outgoing = b""

    def copy(self):
        c = Conn(); c.incoming, c.peer_closed, c.outgoing = self.incoming, self.peer_closed, self.outgoing
        return c

class ModelV2:
    def __init__(self, reserved):
        self.listening = [(3, [])]          # (listener, pending clients)
        self.clients = []                   # client j's conn
        self.open_fds = []                  # (fd, client), consed onto
        self.reserved = list(reserved)

    def copy(self):
        m = ModelV2(self.reserved)
        m.listening = [(l, list(q)) for (l, q) in self.listening]
        m.clients = [c.copy() for c in self.clients]
        m.open_fds = list(self.open_fds)
        return m

    def used_fds(self):
        return self.reserved + [l for (l, _) in self.listening] + [f for (f, _) in self.open_fds]

    def client_of(self, f):
        for (g, j) in self.open_fds:          # ALOOKUP: first match
            if g == f:
                return j if j < len(self.clients) else None
        return None

    # deliver2 / tick2
    def deliver(self, a):
        kind = a[0]
        if kind == "connect":
            l = a[1]
            for i, (g, q) in enumerate(self.listening):
                if g == l:
                    self.listening[i] = (g, q + [len(self.clients)])
                    self.clients.append(Conn())
                    return
        elif kind == "data":
            j, bs = a[1], a[2]
            if j < len(self.clients) and not self.clients[j].peer_closed:
                self.clients[j].incoming += bs
        elif kind == "eof":
            j = a[1]
            if j < len(self.clients):
                self.clients[j].peer_closed = True

    def tick(self, step):
        for a in step:
            self.deliver(a)

    def is_ready(self, fd):
        for (g, q) in self.listening:
            if g == fd:
                if q:
                    return True
                break
        j = self.client_of(fd)
        if j is not None:
            c = self.clients[j]
            return c.incoming != b"" or c.peer_closed
        return False

    # The FFI functions: (output bytes) or None (misuse: the call fails)
    def ffi_poll(self, conf, bytes_in, step):
        if len(conf) != 8 * len(bytes_in):
            return None
        self.tick(step)
        return bytes(1 if self.is_ready(fd) else 0 for fd in bytes_fds(conf))

    def ffi_accept(self, conf, bytes_in):
        if len(conf) != 8 or len(bytes_in) != 9:
            return None
        l = bytes_fd(conf)
        for i, (g, q) in enumerate(self.listening):
            if g == l:
                if not q:
                    return b"\x00" + bytes_in[1:]
                j, rest = q[0], q[1:]
                used = self.used_fds()
                f = 0
                while f in used:
                    f += 1
                self.listening[i] = (g, rest)
                self.open_fds = [(f, j)] + self.open_fds
                return b"\x01" + fd_bytes(f)
        return None

    def ffi_read(self, conf, bytes_in):
        if len(conf) != 8 or not (9 < len(bytes_in)):
            return None
        j = self.client_of(bytes_fd(conf))
        if j is None:
            return None
        n = len(bytes_in) - 9
        c = self.clients[j]
        if c.incoming != b"":
            d, c.incoming = c.incoming[:n], c.incoming[n:]
            return b"\x00" + len(d).to_bytes(8, "big") + d + bytes_in[9 + len(d):]
        if c.peer_closed:
            return b"\x02" + bytes_in[1:]
        return b"\x01" + bytes_in[1:]

    def ffi_write(self, conf, bytes_in):
        if len(conf) < 8:
            return None
        j = self.client_of(bytes_fd(conf[:8]))
        if j is None:
            return None
        self.clients[j].outgoing += conf[8:]
        return bytes_in

    def ffi_close(self, conf, bytes_in):
        if len(conf) != 8:
            return None
        f = bytes_fd(conf)
        if self.client_of(f) is None:
            return None
        self.open_fds = [(g, j) for (g, j) in self.open_fds if g != f]   # ADELKEY
        return bytes_in

    def to_json(self):    # a deep copy: later steps must not change a logged state
        return json.loads(json.dumps(self._json()))

    def _json(self):
        return {"listening": self.listening,
                "clients": [{"incoming": c.incoming.hex(), "peer_closed": c.peer_closed,
                             "outgoing": c.outgoing.hex()} for c in self.clients],
                "open_fds": self.open_fds, "reserved": self.reserved}

# ---------------------------------------------------------------------------
# The server child: socket_ffi.c in a process of its own

def open_fds_now(limit=256):
    fds = []
    for fd in range(limit):
        try:
            fcntl.fcntl(fd, fcntl.F_GETFD)
            fds.append(fd)
        except OSError:
            pass
    return fds

def server_child(cmd_fd, res_fd, port):
    # keep fd 3 free for the listener the constructor creates
    hi_cmd, hi_res = 40, 41
    os.dup2(cmd_fd, hi_cmd); os.dup2(res_fd, hi_res)
    os.close(cmd_fd); os.close(res_fd)
    os.environ["CAKE_ECHO_PORT"] = str(port)
    lib = ctypes.CDLL(LIB)
    fns = {n: getattr(lib, "ffisock_" + n) for n in ["poll", "accept", "read", "write", "close"]}
    for f in fns.values():
        f.argtypes = [ctypes.c_char_p, ctypes.c_long, ctypes.c_char_p, ctypes.c_long]
        f.restype = None
    rin = os.fdopen(hi_cmd, "r"); rout = os.fdopen(hi_res, "w")
    rout.write(json.dumps({"reserved": [fd for fd in open_fds_now() if fd != 3]}) + "\n"); rout.flush()
    for line in rin:
        req = json.loads(line)
        if req["op"] == "peer":
            s = socket.socket(fileno=os.dup(req["fd"]))
            port_ = s.getpeername()[1]; s.close()
            rout.write(json.dumps({"port": port_}) + "\n"); rout.flush(); continue
        if req["op"] == "fds":
            rout.write(json.dumps({"fds": open_fds_now()}) + "\n"); rout.flush(); continue
        conf = bytes.fromhex(req["conf"]); a = ctypes.create_string_buffer(bytes.fromhex(req["bytes"]), len(req["bytes"]) // 2)
        fns[req["op"]](conf, len(conf), a, len(a))
        rout.write(json.dumps({"bytes": a.raw.hex()}) + "\n"); rout.flush()

class Server:
    def __init__(self, port):
        c_r, c_w = os.pipe(); r_r, r_w = os.pipe()
        self.pid = os.fork()
        if self.pid == 0:
            os.close(c_w); os.close(r_r)
            try:
                server_child(c_r, r_w, port)
            finally:
                os._exit(0)
        os.close(c_r); os.close(r_w)
        self.w = os.fdopen(c_w, "w"); self.r = os.fdopen(r_r, "r")
        self.reserved = json.loads(self.r.readline())["reserved"]

    def ask(self, req):
        self.w.write(json.dumps(req) + "\n"); self.w.flush()
        line = self.r.readline()
        if not line:
            raise RuntimeError("server child died (the FFI call aborted)")
        return json.loads(line)

    def call(self, op, conf, bytes_in):
        return bytes.fromhex(self.ask({"op": op, "conf": conf.hex(), "bytes": bytes_in.hex()})["bytes"])

    def stop(self):
        self.w.close()
        os.waitpid(self.pid, 0)

# ---------------------------------------------------------------------------
# A random scenario

class Divergence(Exception):
    pass

def run_scenario(seed, steps, port, log, max_chunk=3000, read_sizes=(1, 2, 7, 100, 4096, 65536),
                 max_write=16000):
    rng = random.Random(seed)
    srv = Server(port)
    model = ModelV2(srv.reserved)
    clients = []            # client j: (socket, local port, eof sent, received bytes)
    pending = []            # the next schedule step (client actions not yet delivered)
    findings = []
    nstep = 0

    def drain():
        for cl in clients:
            s = cl["sock"]
            while True:
                r, _, _ = select.select([s], [], [], 0.002)
                if not r:
                    break
                try:
                    d = s.recv(65536)
                except (ConnectionResetError, OSError):
                    break
                if not d:
                    break
                cl["recv"] += d

    def record(op, conf, bin_, real, exp, before, step=None, extra=None):
        nonlocal nstep
        entry = {"seed": seed, "n": nstep, "op": op, "conf": conf.hex(), "bytes_in": bin_.hex(),
                 "real": real.hex() if real is not None else None,
                 "model": exp.hex() if exp is not None else None,
                 "before": before, "step": step, "after": model.to_json()}
        if extra:
            entry.update(extra)
        log.write(json.dumps(entry) + "\n")
        nstep += 1
        if real != exp:
            findings.append(entry)
            raise Divergence()   # the states no longer correspond: stop this scenario

    try:
        for _ in range(steps):
            open_fds = [f for (f, _) in model.open_fds]
            unread = sum(len(c.incoming) for c in model.clients)
            choice = rng.choices(["client", "poll", "accept", "read", "write", "close"],
                                 weights=[4, 3, 2, 4, 2, 1 if open_fds else 0])[0]
            if choice == "client":
                # planned now, performed just before the poll that delivers it
                nconn = sum(1 for a in pending if a[0] == "connect")
                known = len(clients) + nconn
                live = [j for j in range(known)
                        if not (j < len(clients) and clients[j]["eof"])
                        and not any(a[0] == "eof" and a[1] == j for a in pending)]
                k = rng.choices(["connect", "data", "eof"],
                                weights=[2, 6 if live and unread < 60000 else 0, 1 if live else 0])[0]
                if k == "connect":
                    pending.append(("connect", 3))
                elif k == "data":
                    j = rng.choice(live)
                    pending.append(("data", j,
                                    bytes(rng.randrange(256) for _ in range(rng.randint(1, max_chunk)))))
                else:
                    pending.append(("eof", rng.choice(live)))
                continue
            before = model.to_json()
            if choice == "poll":
                fds = [3] + [f for f in open_fds if rng.random() < 0.8]
                rng.shuffle(fds)
                conf, bin_ = fds_bytes(fds), bytes(len(fds))
                for a in pending:            # the schedule step, in the real world
                    if a[0] == "connect":
                        sk = socket.create_connection(("127.0.0.1", port))
                        clients.append({"sock": sk, "port": sk.getsockname()[1], "eof": False,
                                        "recv": b""})
                    elif a[0] == "data":
                        try:   # after the server closed c's fd, sends may fail: unobservable
                            clients[a[1]]["sock"].sendall(a[2])
                        except (BrokenPipeError, ConnectionResetError):
                            pass
                    else:
                        try:
                            clients[a[1]]["sock"].shutdown(socket.SHUT_WR)
                        except OSError:
                            pass
                        clients[a[1]]["eof"] = True
                time.sleep(SETTLE)
                step = [list(a[:2]) + ([a[2].hex()] if a[0] == "data" else []) for a in pending]
                exp = model.ffi_poll(conf, bin_, pending)
                pending = []
                real = srv.call("poll", conf, bin_)
                record("poll", conf, bin_, real, exp, before, step)
            elif choice == "accept":
                conf, bin_ = fd_bytes(3), bytes(9)
                exp = model.ffi_accept(conf, bin_)
                real = srv.call("accept", conf, bin_)
                extra = None
                if real[0] == 1:
                    port_ = srv.ask({"op": "peer", "fd": bytes_fd(real[1:])})["port"]
                    who = [j for j, cl in enumerate(clients) if cl["port"] == port_]
                    exp_j = model.open_fds[0][1] if exp is not None and exp[0] == 1 else None
                    extra = {"real_client": who[0] if who else None, "model_client": exp_j}
                    if who and exp_j is not None and who[0] != exp_j:
                        findings.append({"seed": seed, "n": nstep, "op": "accept-client",
                                         "real": who[0], "model": exp_j})
                        raise Divergence()
                record("accept", conf, bin_, real, exp, before, extra=extra)
            elif choice == "read" and open_fds:
                fd = rng.choice(open_fds)
                conf, bin_ = fd_bytes(fd), bytes(9 + rng.choice(read_sizes))
                exp = model.ffi_read(conf, bin_)
                real = srv.call("read", conf, bin_)
                record("read", conf, bin_, real, exp, before)
            elif choice == "write" and open_fds:
                fd = rng.choice(open_fds)
                data = bytes(rng.randrange(256) for _ in range(rng.randint(0, max_write)))
                conf, bin_ = fd_bytes(fd) + data, bytes(rng.randint(0, 3))
                exp = model.ffi_write(conf, bin_)
                real = srv.call("write", conf, bin_)
                record("write", conf, bin_, real, exp, before)
                drain()
            elif choice == "close" and open_fds:
                fd = rng.choice(open_fds)
                conf, bin_ = fd_bytes(fd), bytes(rng.randint(0, 3))
                exp = model.ffi_close(conf, bin_)
                real = srv.call("close", conf, bin_)
                record("close", conf, bin_, real, exp, before)
        # what each client received is the model's outgoing log
        time.sleep(SETTLE)
        drain()
        for j, cl in enumerate(clients):
            if cl["recv"] != model.clients[j].outgoing:
                findings.append({"seed": seed, "op": "outgoing", "client": j,
                                 "real_len": len(cl["recv"]), "model_len": len(model.clients[j].outgoing)})
        # the process's other fds did not change (the model's reserved)
        fds_end = srv.ask({"op": "fds"})["fds"]
        expect = sorted(set(model.reserved + [3] + [f for (f, _) in model.open_fds]))
        if sorted(fds_end) != expect:
            findings.append({"seed": seed, "op": "fd-table", "real": fds_end, "model": expect})
    except Divergence:
        pass
    except RuntimeError as e:
        findings.append({"seed": seed, "n": nstep, "op": "abort", "error": str(e)})
    finally:
        for cl in clients:
            cl["sock"].close()
        srv.stop()
    return nstep, findings

def build_lib():
    os.makedirs(os.path.dirname(LIB), exist_ok=True)
    subprocess.check_call(["cc", "-O2", "-shared", "-fPIC", "-o", LIB, FFI_C])

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", type=int, default=20)
    ap.add_argument("--first-seed", type=int, default=1)
    ap.add_argument("--steps", type=int, default=300)
    ap.add_argument("--port", type=int, default=7900)
    ap.add_argument("--log", default=os.path.join(HERE, "build", "trace.jsonl"))
    ap.add_argument("--small", action="store_true",
                    help="small data (for the HOL cross-check): chunks ≤ 12 bytes, reads ≤ 16")
    args = ap.parse_args()
    build_lib()
    total, allf = 0, []
    with open(args.log, "w") as log:
        for i in range(args.seeds):
            seed = args.first_seed + i
            kw = dict(max_chunk=12, read_sizes=(1, 2, 5, 16), max_write=12) if args.small else {}
            n, f = run_scenario(seed, args.steps, args.port + i, log, **kw)
            total += n; allf += f
            print(f"seed {seed}: {n} FFI calls, {len(f)} divergences", flush=True)
    print(f"TOTAL: {total} FFI calls checked, {len(allf)} divergences")
    for f in allf[:20]:
        print(json.dumps({k: v for k, v in f.items() if k not in ("before", "after")})[:600])
    sys.exit(1 if allf else 0)

if __name__ == "__main__":
    main()
