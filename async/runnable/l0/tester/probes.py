#!/usr/bin/env python3
"""
Platform probes for the L0 socket FFI (design/36 §4, phase 2's first job).
Each probe drives the real C (in a child process) with real loopback
clients and prints what the kernel did, so that the L0 world model can be
checked against it before it is frozen.  Not trusted.

Run:  python3 probes.py --lib ../build/libsocket_ffi_l0.dylib [--out FILE]
"""
import argparse, os, platform, socket, struct, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from l0harness import Server, show, revs, ERR

SETTLE = 0.05
PORT = [20000 + os.getpid() % 20000]
OUT = []

def say(*a):
    line = " ".join(str(x) for x in a)
    OUT.append(line); print(line)

def port():
    PORT[0] += 1
    return PORT[0]

def setup(lib):
    s = Server(lib)
    p = port()
    code, l, _, _ = s.listen(p)
    assert code == 0, "listen failed"
    return s, l, p

def client(p):
    c = socket.socket(); c.connect(("127.0.0.1", p)); return c

def rst_close(c):
    c.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0)); c.close()

def pollone(s, fd, ev=3):
    res, flags = s.poll([(fd, ev)])
    return revs(flags[0])

def probe_partial_send(lib):
    say("\n## P1 partial send / EAGAIN: client never reads")
    s, l, p = setup(lib); c = client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    total, sends = 0, []
    for i in range(400):
        r = s.send(f, b"x" * 65536)
        sends.append(r)
        if r[0] != 0:
            break
        total += r[1]
    partial = [r[1] for r in sends if r[0] == 0 and r[1] < 65536]
    say("accepted before refusal:", total, "bytes in", len(sends) - 1, "sends; partial counts:", partial[:5])
    say("last send:", show(sends[-1]))
    say("poll IN|OUT while full:", pollone(s, f))
    c.recv(1 << 20); time.sleep(SETTLE)
    say("after the client reads 1 MiB: poll", pollone(s, f), "; send:", show(s.send(f, b"y" * 65536)))
    c.close(); s.stop()

def probe_reset(lib):
    say("\n## P2 reset by the peer (SO_LINGER 0): recv / poll / send sequence")
    s, l, p = setup(lib); c = client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    rst_close(c); time.sleep(SETTLE)
    say("poll:", pollone(s, f))
    for i in range(3):
        say("recv %d:" % (i + 1), show(s.recv(f, 100)))
    say("poll after:", pollone(s, f))
    for i in range(2):
        say("send %d:" % (i + 1), show(s.send(f, b"z")))
    s.stop()

def probe_reset_unread(lib):
    say("\n## P3 reset with unread data at the server: is the data kept?")
    s, l, p = setup(lib); c = client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.sendall(b"hello"); time.sleep(SETTLE); rst_close(c); time.sleep(SETTLE)
    say("poll:", pollone(s, f))
    for i in range(3):
        r = s.recv(f, 100); say("recv %d:" % (i + 1), show(r), r[3])
    s.stop()

def probe_send_then_reset(lib):
    say("\n## P4 send to a peer that closed normally, then reset")
    s, l, p = setup(lib); c = client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.close(); time.sleep(SETTLE)
    say("poll after peer FIN:", pollone(s, f))
    say("send 1:", show(s.send(f, b"a"))); time.sleep(SETTLE)
    say("poll after (peer answers RST):", pollone(s, f))
    say("send 2:", show(s.send(f, b"b")))
    say("send 3:", show(s.send(f, b"c")))
    say("recv:", show(s.recv(f, 10)))
    s.stop()

def probe_emfile(lib):
    say("\n## P5 out of fds (EMFILE): accept result, listener readiness, recovery")
    s, l, p = setup(lib)
    used = len(s.fds())
    s.rlimit(used + 2)                       # room for 2 more fds (60/61 count)
    cs = [client(p) for _ in range(4)]; time.sleep(SETTLE)
    acc = [s.accept(l) for _ in range(4)]
    say("accepts:", [show(a) for a in acc])
    say("listener poll after EMFILE:", pollone(s, l, 1))
    ok = [a[1] for a in acc if a[0] == 0]
    s.close(ok[0]) if ok else None
    say("after one close, accept:", show(s.accept(l)))
    for i, c in enumerate(cs):
        c.settimeout(0.2)
        try:
            c.sendall(b"ping"); time.sleep(SETTLE); d = c.recv(10)
            say("client %d: recv" % i, d)
        except socket.timeout:
            say("client %d: still connected (no data)" % i)
        except OSError as e:
            say("client %d: error" % i, e.errno, os.strerror(e.errno))
    for c in cs: c.close()
    s.stop()

def probe_rst_on_close(lib):
    say("\n## P6 server closes with unread input: does the client get the response?")
    s, l, p = setup(lib); c = client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.sendall(b"request-1 request-2"); time.sleep(SETTLE)
    s.recv(f, 9)                              # reads only "request-1"
    say("server send:", show(s.send(f, b"response-1")))
    say("server close (unread input remains):", show(s.close(f))); time.sleep(SETTLE)
    try:
        say("client recv:", c.recv(100), "then", c.recv(100))
    except OSError as e:
        say("client recv: error", e.errno, os.strerror(e.errno))
    c.close()
    say("-- the same with the input drained first --")
    c = client(p); time.sleep(SETTLE); _, f, _, _ = s.accept(l)
    c.sendall(b"request-1"); time.sleep(SETTLE); s.recv(f, 100)
    s.send(f, b"response-1"); s.close(f); time.sleep(SETTLE)
    say("client recv:", c.recv(100)); c.close(); s.stop()

def probe_short_reads(lib):
    say("\n## P7 short reads: data arriving between two recvs, no poll in between")
    s, l, p = setup(lib); c = client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.sendall(b"aaaa"); time.sleep(SETTLE)
    r1 = s.recv(f, 100)
    c.sendall(b"bbbb"); time.sleep(SETTLE)
    r2 = s.recv(f, 100)
    say("recv 1:", r1[3], " recv 2 (no poll in between):", r2[3])
    say("recv after empty:", show(s.recv(f, 100)))
    c.sendall(b"cccc"); time.sleep(SETTLE)
    say("then data arrives, recv again (no poll):", s.recv(f, 100)[3])
    c.close(); s.stop()

def probe_aborted(lib):
    say("\n## P8 a pending connection reset before accept")
    s, l, p = setup(lib); c = client(p); time.sleep(SETTLE)
    rst_close(c); time.sleep(SETTLE)
    say("listener poll:", pollone(s, l, 1))
    a = s.accept(l); say("accept:", show(a))
    if a[0] == 0:
        say("  then recv on it:", show(s.recv(a[1], 10)), "; poll:", pollone(s, a[1]))
    say("accept again:", show(s.accept(l)))
    s.stop()

def probe_hup(lib):
    say("\n## P9 HUP: both directions shut; peer FIN only")
    s, l, p = setup(lib); c = client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.shutdown(socket.SHUT_WR); time.sleep(SETTLE)
    say("peer FIN only: poll", pollone(s, f))
    say("our shutdown:", show(s.shutdown(f))); time.sleep(SETTLE)
    say("both shut: poll", pollone(s, f))
    say("send after our shutdown:", show(s.send(f, b"x")))
    c.close(); time.sleep(SETTLE)
    say("peer closed too: poll", pollone(s, f))
    s.stop()

def probe_misc(lib):
    say("\n## P10 misc: NVAL, EBADF, port in use, unknown errno")
    s, l, p = setup(lib)
    say("poll a closed fd 40:", pollone(s, 40))
    say("recv on fd 40:", show(s.recv(40, 10)))
    say("send on the listener:", show(s.send(l, b"x")))
    say("accept on fd 0 (not a socket):", show(s.accept(0)))
    say("listen on the same port again:", show(s.listen(p)))
    say("child fds:", s.fds())
    s.stop()

PROBES = [probe_partial_send, probe_reset, probe_reset_unread, probe_send_then_reset,
          probe_emfile, probe_rst_on_close, probe_short_reads, probe_aborted, probe_hup,
          probe_misc]

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--out")
    args = ap.parse_args()
    say("# L0 platform probes:", platform.system(), platform.release(), platform.machine())
    for pr in PROBES:
        try:
            pr(os.path.abspath(args.lib))
        except Exception as e:
            say("PROBE FAILED:", pr.__name__, repr(e))
    if args.out:
        open(args.out, "w").write("\n".join(OUT) + "\n")
