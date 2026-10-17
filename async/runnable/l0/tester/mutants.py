#!/usr/bin/env python3
"""Mutation test of the conformance checker: each mutant is a real probe
log with one observation changed to something the L0 world forbids; the
checker must report a FINDING for every one.  Not trusted."""
import copy, json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import l0check

def mutate(runs, name, pred, f):
    log = copy.deepcopy(runs[name])
    for ev in log:
        if ev[0] == "call" and pred(ev):
            ev[4] = f(bytes.fromhex(ev[4])).hex()
            return log
    raise SystemExit("no call to mutate in %s" % name)

def nth(n, pred):
    """The n-th call (1-based) satisfying pred"""
    seen = [0]
    def p(ev):
        if pred(ev):
            seen[0] += 1
            return seen[0] == n
        return False
    return p

def setb(b, i, v):
    b = bytearray(b); b[i] = v; return bytes(b)

def main(path):
    runs = json.load(open(path))
    M = [
      ("recv returns other bytes", "P7_arrivals_between_calls",
       lambda ev: ev[1] == "recv" and bytes.fromhex(ev[4])[0] == 0,
       lambda o: setb(o, 13, o[13] ^ 1)),
      ("recv says EAGAIN although data is readable", "P3_reset_unread",
       lambda ev: ev[1] == "recv", lambda o: bytes([1]) + bytes(12) + o[13:]),
      ("accept returns an fd that is not the lowest free", "P1_partial_send",
       lambda ev: ev[1] == "accept", lambda o: o[:8] + bytes([o[8] + 3]) + o[9:]),
      ("poll says not readable after recv reported the reset", "P2_reset",
       nth(2, lambda ev: ev[1] == "poll" and len(bytes.fromhex(ev[4])) == 24),
       lambda o: bytes(13) + o[13:22] + bytes(2)),
      ("send accepts more than offered", "P1_partial_send",
       lambda ev: ev[1] == "send" and bytes.fromhex(ev[4])[0] == 0,
       lambda o: o[:1] + (10 ** 6).to_bytes(8, "big") + o[9:]),
      ("recv reports EOF while data is unread", "P3_reset_unread",
       lambda ev: ev[1] == "recv", lambda o: bytes(13) + o[13:]),
      ("NVAL on an open fd", "P9_hup",
       lambda ev: ev[1] == "poll", lambda o: o[:22] + (32).to_bytes(2, "little") + o[24:]),
      ("EAGAIN from accept with a connection pending", "P8_aborted_pending",
       lambda ev: ev[1] == "accept", lambda o: bytes([1]) + bytes(12)),
      ("connect returns an fd that is not the lowest free", "P11_connect",
       lambda ev: ev[1] == "connect", lambda o: o[:8] + bytes([o[8] + 3]) + o[9:]),
      ("connerr reports an error twice", "P12_refused",
       nth(2, lambda ev: ev[1] == "connerr"), lambda o: bytes([4]) + bytes(7) + bytes([1]) + o[9:]),
      ("recv data on a refused connect", "P12_refused",
       lambda ev: ev[1] == "recv", lambda o: bytes(8) + bytes([1]) + bytes(4) + b"x" + o[14:]),
    ]
    bad = 0
    for desc, name, pred, f in M:
        r = l0check.check(mutate(runs, name, pred, f))
        ok = r is not None
        bad += not ok
        print("%-55s %s" % (desc, "caught: %s" % r[1] if ok else "MISSED"))
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main(sys.argv[1])
