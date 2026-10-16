#!/usr/bin/env python3
"""
Platform probes = CONFORMANCE TESTS for the L0 socket FFI (design/36 §4).
Each probe drives the real C (socket_ffi_l0.c, in a child process) with
real loopback clients, prints what the kernel did, and logs the run.  The
logs are then checked against the L0 world (l0check.py): every observation
must be a behaviour of the model; anything else is a FINDING.  Not trusted.

Run:  python3 probes.py --lib ../build/libsocket_ffi_l0.dylib --out probes-<platform>.txt
      (also writes the run logs to probes-<platform>.json and checks them)
"""
import argparse, json, os, platform, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from l0harness import Server, show, revs
import l0check

SETTLE = 0.05
PORT = [20000 + os.getpid() % 20000]
OUT = []
RUNS = {}

def say(*a):
    line = " ".join(str(x) for x in a)
    OUT.append(line); print(line)

def setup(lib):
    s = Server(lib); s.start_log()
    PORT[0] += 1
    code, l, _, _ = s.listen(PORT[0])
    assert code == 0, "listen failed"
    return s, l, PORT[0]

def finish(name, s):
    s.log.append(["fds", s.fds()])
    RUNS[name] = s.log
    s.stop()

def pollone(s, fd, ev=3):
    res, flags = s.poll([(fd, ev)])
    return revs(flags[0])

def p1_partial_send(lib):
    say("\n## P1 partial send / EAGAIN: a client that never reads")
    s, l, p = setup(lib); c = s.client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    total, sends = 0, []
    for i in range(400):
        r = s.send(f, b"x" * 65536); sends.append(r)
        if r[0] != 0:
            break
        total += r[1]
    say("accepted before refusal:", total, "bytes in", len(sends) - 1, "sends; partial counts:",
        [r[1] for r in sends if r[0] == 0 and r[1] < 65536][:5])
    say("last send:", show(sends[-1]))
    say("poll IN|OUT while full:", pollone(s, f))
    c.recv(1 << 20); time.sleep(SETTLE)
    say("after the client reads up to 1 MiB: poll", pollone(s, f), "; send:", show(s.send(f, b"y" * 65536)))
    c.close(); finish("P1_partial_send", s)

def p2_reset(lib):
    say("\n## P2 reset by the peer (SO_LINGER 0): recv / poll / send sequence")
    s, l, p = setup(lib); c = s.client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.rst(); time.sleep(SETTLE)
    say("poll:", pollone(s, f))
    for i in range(3):
        say("recv %d:" % (i + 1), show(s.recv(f, 100)))
    say("poll after:", pollone(s, f))
    for i in range(2):
        say("send %d:" % (i + 1), show(s.send(f, b"z")))
    finish("P2_reset", s)

def p3_reset_unread(lib):
    say("\n## P3 reset with unread data at the server: is the data kept?")
    s, l, p = setup(lib); c = s.client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.send(b"hello"); time.sleep(SETTLE); c.rst(); time.sleep(SETTLE)
    say("poll:", pollone(s, f))
    for i in range(3):
        r = s.recv(f, 100); say("recv %d:" % (i + 1), show(r), r[3])
    finish("P3_reset_unread", s)

def p4_send_then_reset(lib):
    say("\n## P4 send to a peer that closed normally, then reset")
    s, l, p = setup(lib); c = s.client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.close(); time.sleep(SETTLE)
    say("poll after peer FIN:", pollone(s, f))
    say("send 1:", show(s.send(f, b"a"))); time.sleep(SETTLE)
    say("poll after (peer answers RST):", pollone(s, f))
    say("send 2:", show(s.send(f, b"b")))
    say("send 3:", show(s.send(f, b"c")))
    say("recv:", show(s.recv(f, 10)))
    finish("P4_send_then_reset", s)

def p5_emfile(lib):
    say("\n## P5 out of fds (EMFILE): accept, listener readiness, the clients' fate")
    s, l, p = setup(lib)
    s.rlimit(l + 3)                          # fds l+1, l+2 free below the limit
    cs = [s.client(p) for _ in range(4)]; time.sleep(SETTLE)
    acc = [s.accept(l) for _ in range(4)]
    say("accepts:", [show(a) for a in acc])
    say("listener poll after EMFILE:", pollone(s, l, 1))
    ok = [a[1] for a in acc if a[0] == 0]
    if ok:
        s.close(ok[0])
    say("after one close, accept:", show(s.accept(l)))
    for i, c in enumerate(cs):
        try:
            c.send(b"ping")
        except OSError as e:
            say("client %d: send error %d" % (i, e.errno)); continue
        time.sleep(SETTLE); d = c.recv(10)
        say("client %d:" % i, "still connected (no data)" if d is None else d)
    for c in cs:
        c.close()
    finish("P5_emfile", s)

def p6_rst_on_close(lib):
    say("\n## P6 server closes with unread input: does the client get the response?")
    s, l, p = setup(lib); c = s.client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.send(b"request-1 request-2"); time.sleep(SETTLE)
    s.recv(f, 9)
    say("server send:", show(s.send(f, b"response-1")))
    say("server close (unread input remains):", show(s.close(f))); time.sleep(SETTLE)
    say("client recv:", c.recv(100))
    c.close()
    say("-- the same with the input drained first --")
    c = s.client(p); time.sleep(SETTLE); _, f, _, _ = s.accept(l)
    c.send(b"request-1"); time.sleep(SETTLE); s.recv(f, 100)
    s.send(f, b"response-1"); s.close(f); time.sleep(SETTLE)
    say("client recv:", c.recv(100)); c.close()
    finish("P6_rst_on_close", s)

def p7_short_reads(lib):
    say("\n## P7 arrivals between calls: data after an EAGAIN, no poll in between")
    s, l, p = setup(lib); c = s.client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.send(b"aaaa"); time.sleep(SETTLE)
    r1 = s.recv(f, 100)
    c.send(b"bbbb"); time.sleep(SETTLE)
    r2 = s.recv(f, 100)
    say("recv 1:", r1[3], " recv 2 (no poll in between):", r2[3])
    say("recv when empty:", show(s.recv(f, 100)))
    c.send(b"cccc"); time.sleep(SETTLE)
    say("then data arrives; recv again (no poll):", s.recv(f, 100)[3])
    say("a 2-byte recv of 4 bytes:", s.recv(f, 2)[3] if False else "-")
    c.send(b"dddd"); time.sleep(SETTLE)
    say("recv(2) of 4 available:", s.recv(f, 2)[3], " then:", s.recv(f, 100)[3])
    c.close(); finish("P7_arrivals_between_calls", s)

def p8_aborted(lib):
    say("\n## P8 a pending connection reset before accept")
    s, l, p = setup(lib); c = s.client(p); time.sleep(SETTLE)
    c.rst(); time.sleep(SETTLE)
    say("listener poll:", pollone(s, l, 1))
    a = s.accept(l); say("accept:", show(a))
    if a[0] == 0:
        say("  then recv on it:", show(s.recv(a[1], 10)), "; poll:", pollone(s, a[1]))
    say("accept again:", show(s.accept(l)))
    finish("P8_aborted_pending", s)

def p9_hup(lib):
    say("\n## P9 HUP: peer FIN only; both directions shut")
    s, l, p = setup(lib); c = s.client(p); time.sleep(SETTLE)
    _, f, _, _ = s.accept(l)
    c.shutdown(); time.sleep(SETTLE)
    say("peer FIN only: poll", pollone(s, f))
    say("our shutdown:", show(s.shutdown(f))); time.sleep(SETTLE)
    say("both shut: poll", pollone(s, f))
    say("send after our shutdown:", show(s.send(f, b"x")))
    c.close(); time.sleep(SETTLE)
    say("peer closed too: poll", pollone(s, f))
    finish("P9_hup", s)

def p10_misc(lib):
    say("\n## P10 misc: NVAL, EBADF, wrong kinds of fd, port in use")
    s, l, p = setup(lib)
    say("poll a closed fd 40:", pollone(s, 40))
    say("recv on fd 40:", show(s.recv(40, 10)))
    say("send on the listener:", show(s.send(l, b"x")))
    say("accept on fd 0 (not a socket):", show(s.accept(0)))
    say("listen on the same port again:", show(s.listen(p)))
    say("close fd 40:", show(s.close(40)))
    finish("P10_misc", s)

PROBES = [p1_partial_send, p2_reset, p3_reset_unread, p4_send_then_reset, p5_emfile,
          p6_rst_on_close, p7_short_reads, p8_aborted, p9_hup, p10_misc]

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
    say("\n# Conformance (l0check: is each run a behaviour of the L0 world?)")
    for name, log in RUNS.items():
        r = l0check.check(log)
        say("%-28s %s" % (name, "conforms" if r is None else "FINDING at step %d: %s" % r))
        for w in l0check.WARN:
            say("    warning:", w)
    if args.out:
        open(args.out, "w").write("\n".join(OUT) + "\n")
        json.dump(RUNS, open(os.path.splitext(args.out)[0] + ".json", "w"))
