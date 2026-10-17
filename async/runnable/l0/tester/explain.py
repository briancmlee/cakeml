#!/usr/bin/env python3
"""Print a run's events up to a step, decoded (for reading findings)"""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from l0harness import ERR, revs, poll_entries, from_native
runs = json.load(open(sys.argv[1])); log = runs[sys.argv[2]]; upto = int(sys.argv[3])
for i, ev in enumerate(log[:upto + 1]):
    if ev[0] == "call":
        _, name, conf, alen, out = ev[:5]; c, o = bytes.fromhex(conf), bytes.fromhex(out)
        code, val = o[0], int.from_bytes(o[1:9], "big")
        res = ("OK %d" % val) if code == 0 else ERR.get(code, code)
        if name == "poll":
            res += " " + " ".join("%d:%s" % (f, revs(from_native(r) or 0) if from_native(r) is not None else hex(r))
                                  for (f, _, r) in poll_entries(o))
            print(i, "poll", res)
        elif name == "send":
            print(i, "send fd %d len %d ->" % (int.from_bytes(c[:8], "big"), len(c) - 8), res)
        elif name == "recv":
            print(i, "recv fd %d n %d ->" % (int.from_bytes(c, "big"), alen - 13), res, o[13:13+val][:20] if code == 0 else "")
        else:
            print(i, name, int.from_bytes(c, "big"), "->", res)
    else:
        e = list(ev)
        if e[0] == "data": e[2] = "%d bytes" % (len(e[2]) // 2)
        print(i, *e)
