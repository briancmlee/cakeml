#!/usr/bin/env python3
"""Demo of the verified chat server (spec/ChatSpec).  Not trusted: it only
drives the server and checks what ChatSpec promises:

 - every client receives every complete line, the sender included;
 - all clients receive them in ONE order (the order the server read them);
 - a client receives exactly the lines read after it joined (no backlog);
 - a partial line (no newline yet) is not relayed until it is completed.
"""
import argparse, os, socket, subprocess, sys, time

PORT = int(os.environ.get("PORT", "7860"))


def log(msg):
    print("%8.3f  %s" % (time.time() - T0, msg), flush=True)


def connect(name):
    s = socket.create_connection(("127.0.0.1", PORT))
    s.settimeout(0.05)
    log("%s connects" % name)
    return s


def drain(s, secs=0.6):
    buf, end = b"", time.time() + secs
    while time.time() < end:
        try:
            chunk = s.recv(4096)
            if not chunk:
                break
            buf += chunk
        except socket.timeout:
            pass
    return buf


def send(name, s, data):
    log("%s sends %r" % (name, data))
    s.sendall(data)


def main():
    global T0
    ap = argparse.ArgumentParser()
    ap.add_argument("--server", default="build/chat_server")
    args = ap.parse_args()
    T0 = time.time()
    env = dict(os.environ, CAKE_ECHO_PORT=str(PORT))
    proc = subprocess.Popen([args.server], env=env, stderr=subprocess.PIPE,
                            stdin=subprocess.DEVNULL, text=True)
    log("server: " + proc.stderr.readline().strip())
    for _ in range(100):
        try:
            socket.create_connection(("127.0.0.1", PORT), timeout=1).close()
            break
        except OSError:
            time.sleep(0.05)
    got = {}
    try:
        alice, bob = connect("alice"), connect("bob")
        time.sleep(0.3)                      # let the server accept both
        send("alice", alice, b"hello from alice\n")
        send("bob", bob, b"hi alice, bob here\n")
        send("bob", bob, b"half a li")       # no newline yet
        time.sleep(0.3)
        carol = connect("carol")             # joins late: no backlog
        time.sleep(0.3)
        send("bob", bob, b"ne, now finished\n")
        send("carol", carol, b"carol: two\nlines at once\n")
        for name, s in (("alice", alice), ("bob", bob), ("carol", carol)):
            got[name] = drain(s)
            log("%s received %r" % (name, got[name]))
    finally:
        proc.kill()

    # The checks ChatSpec guarantees (chat_safe) and the demo's liveness
    lines = lambda b: b.split(b"\n")[:-1]
    a, b, c = (lines(got[n]) for n in ("alice", "bob", "carol"))
    ok = True
    def check(cond, what):
        nonlocal ok
        print("  [%s] %s" % ("ok" if cond else "FAIL", what))
        ok = ok and cond
    print()
    check(a == b, "alice and bob received the same lines, in the same order")
    check(len(a) == 5, "they received all 5 lines, their own included")
    check(c == a[-3:], "carol received exactly the lines read after she joined")
    check(b"half a line, now finished" in a and b"half a li" not in a,
          "the partial line was relayed only once complete")
    print("\nRESULT:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
