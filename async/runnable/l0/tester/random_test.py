#!/usr/bin/env python3
"""
Randomised conformance test of the L0 socket FFI against the L0 world.
Each scenario interleaves, at random, real loopback client actions
(connect, send, FIN, RST, read some or nothing) and server calls (poll,
accept, recv of random sizes, sends up to 256 KiB so that they go partial,
shutdown, close with or without unread input), sometimes under a low fd
limit (EMFILE), sometimes without settling time (arrivals between calls).
Every run is checked by l0check.  Not trusted.

Usage: random_test.py --lib ../build/libsocket_ffi_l0.dylib --seeds 40 --steps 150
       [--log runs.json]
"""
import argparse, json, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from l0harness import Server
import l0check

def scenario(lib, seed, steps, port):
    rnd = random.Random(seed)
    s = Server(lib); s.start_log()
    code, l, _, _ = s.listen(port)
    assert code == 0
    if rnd.random() < 0.3:
        s.rlimit(l + 1 + rnd.randint(1, 3))           # EMFILE after a few connections
    clients, live = [], []                            # live: clients not closed
    fds = []                                          # the server's open connection fds
    stats = {"partial": 0, "eagain_send": 0, "reset_seen": 0, "emfile": 0, "short": 0,
             "eof": 0, "aborted_close": 0}
    unread = {}                                       # fd -> bytes the server may not have read
    for _ in range(steps):
        r = rnd.random()
        try:
            if r < 0.12 and len(clients) < 8:
                c = s.client(port); clients.append(c); live.append(c)
            elif r < 0.30 and live:
                c = rnd.choice(live); c.send(bytes(rnd.randrange(256) for _ in range(rnd.choice([1, 5, 300, 5000]))))
            elif r < 0.34 and live:
                c = rnd.choice(live); c.shutdown()
            elif r < 0.38 and live:
                c = rnd.choice(live); live.remove(c); c.close()
            elif r < 0.41 and live:
                c = rnd.choice(live); live.remove(c); c.rst()
            elif r < 0.47 and live:
                c = rnd.choice(live); c.recv(rnd.choice([1, 100, 1 << 20]), timeout=0.01)
            elif r < 0.55:
                ents = [(l, 1)] + [(f, rnd.choice([1, 2, 3])) for f in fds]
                s.poll(ents)
            elif r < 0.63:
                code, f, _, _ = s.accept(l)
                if code == 0: fds.append(f)
                if code == 10: stats["emfile"] += 1
            elif r < 0.78 and fds:
                f = rnd.choice(fds); n = rnd.choice([1, 3, 64, 4096, 65536])
                code, val, _, d = s.recv(f, n)
                if code == 0 and val == 0: stats["eof"] += 1
                if code == 0 and 0 < val < n: stats["short"] += 1
                if code == 5: stats["reset_seen"] += 1
            elif r < 0.90 and fds:
                f = rnd.choice(fds)
                n = rnd.choice([10, 1000, 70000, 1 << 20, 2 << 20])
                code, val, _, _ = s.send(f, b"s" * n)
                if code == 0 and val < n: stats["partial"] += 1
                if code == 1: stats["eagain_send"] += 1
            elif r < 0.93 and fds:
                s.shutdown(rnd.choice(fds))
            elif r < 0.97 and fds:
                f = rnd.choice(fds); fds.remove(f)
                if rnd.random() < 0.5:
                    stats["aborted_close"] += 1        # closed without reading first
                s.close(f)
            if rnd.random() < 0.5:
                time.sleep(0.002)
        except OSError:
            pass                                       # a client socket error: the peer's business
    for c in live:
        try: c.close()
        except OSError: pass
    time.sleep(0.01)
    s.log.append(["fds", s.fds()])
    s.stop()
    return s.log, stats

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--seeds", type=int, default=40)
    ap.add_argument("--steps", type=int, default=150)
    ap.add_argument("--log")
    args = ap.parse_args()
    lib = os.path.abspath(args.lib)
    runs, tot, findings, warns, calls = {}, {}, 0, 0, 0
    base = 30000 + os.getpid() % 20000
    for seed in range(args.seeds):
        log, st = scenario(lib, seed, args.steps, base + seed)
        runs["seed%d" % seed] = log
        calls += sum(1 for ev in log if ev[0] == "call")
        for k, v in st.items(): tot[k] = tot.get(k, 0) + v
        r = l0check.check(log)
        warns += len(l0check.WARN)
        if r is not None:
            findings += 1
            print("seed %d: FINDING at step %d: %s" % (seed, r[0], r[1]))
        for w in l0check.WARN:
            print("seed %d: warning: %s" % (seed, w))
    print("%d scenarios, %d calls: %d findings, %d warnings" % (args.seeds, calls, findings, warns))
    print("exercised:", tot)
    if args.log:
        json.dump(runs, open(args.log, "w"))
    sys.exit(1 if findings else 0)
