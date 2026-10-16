#!/usr/bin/env python3
"""
Conformance checker: is a logged run of the real L0 C (socket_ffi_l0.c)
a behaviour of the L0 world (async/honest-l0/honestL0WorldScript.sml)?
Not trusted: it only checks.

The model is an over-approximation: the world chooses (choices) and the
environment decides WHEN each client action reaches the server's kernel.
The checker therefore keeps a SET of possible model states:
  - client actions (connect, data, EOF, reset) are "in transit" until a
    call's result requires them; they are then delivered, as few as
    possible (delivering later is always still possible, so the fewest is
    the most permissive choice);
  - world choices whose effect is visible only later (EMFILE dropping a
    connection or not, a reset keeping the unread input or not) branch;
  - choices visible at once (short reads, send counts, transient errors,
    ERR/HUP shown or not) are read off the observation.
A call that no state explains is a FINDING: the real system did something
the model says it cannot.

Usage:  l0check.py LOG.json      (a log written by conformance.py)
"""
import copy, json, sys

E = {"EAGAIN": 1, "EINTR": 2, "EINPROGRESS": 3, "ECONNREFUSED": 4, "ECONNRESET": 5,
     "EPIPE": 6, "ECONNABORTED": 7, "ETIMEDOUT": 8, "ENOTCONN": 9, "EMFILE": 10,
     "ENFILE": 11, "ENOBUFS": 12, "ENOMEM": 13, "EADDRINUSE": 14, "EACCES": 15,
     "EBADF": 16, "ENOTSOCK": 17, "EINVAL": 18}
# POSIX 2.3: any error "under circumstances other than those described";
# the rely ([A2]) excludes EAGAIN.  Observations explained only this way
# are reported as warnings.
def transient_ok(code):
    return code not in (0, E["EAGAIN"])
IN, OUT, ERR, HUP, NVAL = 1, 2, 4, 8, 16


class Chan:
    def __init__(self):
        self.inbox = b""; self.peer_eof = False; self.err = None; self.broken = False
        self.shut = False; self.sent = b""; self.closed = False; self.aborted = False
        self.connecting = False

    def key(self):
        return (self.inbox, self.peer_eof, self.err, self.broken, self.shut,
                self.sent, self.closed, self.aborted, self.connecting)


class State:
    def __init__(self, reserved, fd_limit):
        self.listeners = []          # [fd, port, [chan]]
        self.chans = []
        self.open_fds = []           # [(fd, j)], consed onto
        self.reserved = list(reserved)
        self.fd_limit = fd_limit
        self.chan_of_client = {}     # client id -> channel
        self.connects = []           # in transit: [(client, port)], in connect order
        self.pending = {}            # client id -> [(kind, payload, optional)]
        self.conn_chans = []         # channels made by sys_connect, in order

    def key(self):
        return (json.dumps(self.listeners), tuple(c.key() for c in self.chans),
                tuple(self.open_fds), tuple(self.reserved), self.fd_limit,
                tuple(sorted(self.chan_of_client.items())), tuple(self.connects),
                tuple(self.conn_chans),
                json.dumps({k: [(a, p.hex() if isinstance(p, bytes) else p, o) for (a, p, o) in v]
                            for k, v in sorted(self.pending.items())}))

    # -- the model's definitions (honestL0World) -------------------------
    def used(self):
        return self.reserved + [l[0] for l in self.listeners] + [f for (f, _) in self.open_fds]

    def chan_of(self, f):
        for (g, j) in self.open_fds:
            if g == f:
                return j
        return None

    def listener(self, f):
        for l in self.listeners:
            if l[0] == f:
                return l
        return None

    def lowest_fd(self):
        """[P 2.6]: the lowest numbered available fd"""
        u = set(self.used()); f = 0
        while f in u:
            f += 1
        return f

    def fd_free(self):
        return self.lowest_fd() < self.fd_limit

    def reset(self, j, keep, e=None):
        c = self.chans[j]
        if not c.broken:
            c.broken = True; c.err = E["ECONNRESET"] if e is None else e
            if not keep:
                c.inbox = b""

    # -- delivering the environment's arrivals ---------------------------
    def deliver_connect(self):
        """The oldest connect in transit (LIncoming)"""
        client, port = self.connects.pop(0)
        for l in self.listeners:
            if l[1] == port:
                l[2].append(len(self.chans))
                self.chan_of_client[client] = len(self.chans)
                self.chans.append(Chan())
                return
        raise Inconsistent("connect to a port with no listener")

    def deliver_next(self, client, keep=True):
        """The client's next action in transit (skipping optional ones is
        done by the caller); returns its kind"""
        kind, payload, _ = self.pending[client].pop(0)
        j = self.chan_of_client[client]
        c = self.chans[j]
        if c.connecting:                 # the peer acts: the connect completed first
            c.connecting = False
        if kind == "data":
            if not c.peer_eof and not c.broken:
                if c.closed:
                    c.aborted = True
                else:
                    c.inbox += payload
        elif kind == "eof":
            if not c.broken:
                c.peer_eof = True
        elif kind == "reset":
            self.reset(j, keep)
        return kind


class Inconsistent(Exception):
    pass


def options(st, client):
    """The states after delivering 0, 1, ... of the client's actions in
    transit (optional ones may be skipped; a reset may keep or lose the
    unread input): a list of (states, how many delivered)"""
    out = [(st, 0)]
    frontier = [st]
    n = len(st.pending.get(client, []))
    for k in range(n):
        nxt = []
        for s in frontier:
            if not s.pending.get(client):
                continue
            kind, _, opt = s.pending[client][0]
            if opt:                                   # skip it
                s2 = copy.deepcopy(s); s2.pending[client].pop(0); nxt.append(s2)
            for keep in ([True, False] if kind == "reset" else [True]):
                s2 = copy.deepcopy(s); s2.deliver_next(client, keep); nxt.append(s2)
        frontier = nxt
        out += [(s, k + 1) for s in nxt]
    return out


def client_of_chan(st, j):
    for cl, jj in st.chan_of_client.items():
        if jj == j:
            return cl
    return None


def with_deliveries(states, j, ok):
    """For each state, the fewest deliveries to channel j's client that make
    ok(state) true; all such states"""
    res = []
    for st in states:
        cl = client_of_chan(st, j)
        found = None
        for (s, k) in (options(st, cl) if cl is not None else [(st, 0)]):
            if found is not None and k > found:
                break
            if ok(s):
                found = k; res.append(s)
    return res


def with_connects(states, ok):
    res = []
    for st in states:
        s = st
        for k in range(len(st.connects) + 1):
            if k:
                s = copy.deepcopy(s); s.deliver_connect()
            if ok(s):
                res.append(s); break
    return res


def completions(states, j, fail_codes=(E["ECONNREFUSED"],)):
    """A pending connect may complete at any moment (LConnUp / LConnFail):
    each state, and if channel j is still connecting, its completions"""
    res = []
    for st in states:
        res.append(st)
        if j is not None and j < len(st.chans) and st.chans[j].connecting:
            s = copy.deepcopy(st); s.chans[j].connecting = False; res.append(s)
            for e in fail_codes:
                s = copy.deepcopy(st); c = s.chans[j]
                c.connecting = False; c.broken = True; c.err = e; res.append(s)
    return res


def chan_states(states, f, fail_codes=(E["ECONNREFUSED"],)):
    """completions for the channel of fd f (in each state)"""
    res = []
    for st in states:
        res += completions([st], st.chan_of(f), fail_codes)
    return res


# -- revents (chan_revents / fd_revents) ---------------------------------

def revents_ok(st, f, ev, r):
    j = st.chan_of(f)
    if j is not None:
        c = st.chans[j]
        if c.connecting:
            return r == 0                       # writable only once established
        want_in = bool(ev & IN) and bool(c.inbox or c.peer_eof or c.broken or c.err)
        if bool(r & IN) != want_in: return False
        if (r & OUT) and not (ev & OUT): return False          # OUT only if requested
        if (r & ERR) and not (c.err is not None or c.broken or c.shut): return False
        if (r & HUP) and not (c.broken or c.peer_eof or c.shut): return False
        return not (r & NVAL)
    l = st.listener(f)
    if l is not None:
        return r == (IN if (ev & IN) and l[2] else 0)
    if f in st.reserved:
        return True
    return r == NVAL


def check_poll(states, conf, out):
    block, ents = conf[0], [(int.from_bytes(conf[1 + 9 * i:9 + 9 * i], "big"), conf[9 + 9 * i])
                            for i in range((len(conf) - 1) // 9)]
    code, val, revs = out[0], int.from_bytes(out[1:9], "big"), out[13:]
    if code:
        if transient_ok(code) and not any(revs):
            WARN.append("poll error %d" % code); return states
        raise Inconsistent("poll error %d" % code)
    if val != sum(1 for r in revs if r):
        raise Inconsistent("poll count %d" % val)
    for (f, ev), r in zip(ents, revs):
        def ok(s, f=f, ev=ev, r=r):
            return revents_ok(s, f, ev, r)
        new = []
        for st in chan_states(states, f):
            j = st.chan_of(f)
            if j is not None:
                new += with_deliveries([st], j, ok)
            elif st.listener(f) is not None:
                new += with_connects([st], ok)
            elif ok(st):
                new.append(st)
        states = new
        if not states:
            raise Inconsistent("poll fd %d revents %d" % (f, r))
    return states


def check_accept(states, conf, out):
    l = int.from_bytes(conf, "big")
    code, val = out[0], int.from_bytes(out[1:9], "big")
    res = []
    for st in states:
        if st.listener(l) is None:
            if code: res.append(st)                  # EBADF / the world's misuse error
            continue
        if code == E["EAGAIN"]:
            if not st.listener(l)[2]: res.append(st)
            continue
        for s in with_connects([st], lambda s: bool(s.listener(l)[2])):
            j = s.listener(l)[2][0]
            if code == 0:
                if s.fd_free() and val == s.lowest_fd():
                    s2 = copy.deepcopy(s); s2.listener(l)[2].pop(0)
                    s2.open_fds.insert(0, (val, j)); res.append(s2)
            elif code == E["EMFILE"] and not s.fd_free():
                res.append(copy.deepcopy(s))                  # stays queued (Linux)
                s2 = copy.deepcopy(s); s2.listener(l)[2].pop(0); s2.reset(j, False)
                res.append(s2)                               # dropped, peer reset (macOS)
            # accept_aborts: the first pending connection has broken
            for s3 in [] if code == 0 else with_deliveries([s], j, lambda x: x.chans[j].broken):
                s4 = copy.deepcopy(s3); s4.listener(l)[2].pop(0); res.append(s4)
    return res


def check_recv(states, conf, out, alen):
    f = int.from_bytes(conf, "big")
    code, val = out[0], int.from_bytes(out[1:9], "big")
    data = out[13:13 + val] if code == 0 else b""
    res = []
    for st in chan_states(states, f, (code,) if code else (E["ECONNREFUSED"],)):
        j = st.chan_of(f)
        if j is None:
            if code: res.append(st)
            continue
        if st.chans[j].connecting:
            if code: res.append(st)               # pending_err: the world's choice
            continue
        if code == 0 and val > 0:
            def ok(s): return len(s.chans[j].inbox) >= val and s.chans[j].inbox[:val] == data
            for s in with_deliveries([st], j, ok):
                s2 = copy.deepcopy(s); s2.chans[j].inbox = s2.chans[j].inbox[val:]; res.append(s2)
        elif code == 0:                                   # EOF: orderly shutdown, or broken
            def ok(s):
                c = s.chans[j]; return not c.inbox and c.err is None and (c.peer_eof or c.broken)
            res += with_deliveries([st], j, ok)
        elif code == E["EAGAIN"]:
            c = st.chans[j]
            if not c.inbox and c.err is None and not c.peer_eof and not c.broken:
                res.append(st)
        else:
            def ok(s, code=code):                         # the pending error ...
                c = s.chans[j]; return not c.inbox and c.err == code
            for s in with_deliveries([st], j, ok):
                s2 = copy.deepcopy(s); s2.chans[j].err = None; res.append(s2)
            def ok2(s):                                   # ... or broken_recv
                c = s.chans[j]; return not c.inbox and c.err is None and c.broken
            res += with_deliveries([st], j, ok2)
    return res


def check_send(states, conf, out):
    f = int.from_bytes(conf[:8], "big"); bs = conf[8:]
    code, val = out[0], int.from_bytes(out[1:9], "big")
    res = []
    for st in chan_states(states, f, (code,) if code else (E["ECONNREFUSED"],)):
        j = st.chan_of(f)
        if j is None:
            if code: res.append(st)
            continue
        c = st.chans[j]
        if c.connecting:
            if code: res.append(st)               # pending_err
            continue
        if code == 0:
            if not c.broken and not c.shut and val <= len(bs) and (val > 0 or not bs):
                s2 = copy.deepcopy(st); s2.chans[j].sent += bs[:val]; res.append(s2)
        elif code == E["EAGAIN"]:
            if not c.broken and not c.shut and bs:
                res.append(st)
        else:
            if code == E["EPIPE"] and c.shut and not c.broken:
                res.append(st)
            # broken: the pending error (cleared), or broken_send (kept)
            for s in with_deliveries([st], j, lambda s, code=code: s.chans[j].broken and s.chans[j].err == code):
                s2 = copy.deepcopy(s); s2.chans[j].err = None; res.append(s2)
            res += with_deliveries([st], j, lambda s: s.chans[j].broken)
    return res


def check_shutdown(states, conf, out):
    f = int.from_bytes(conf, "big"); code = out[0]
    res = []
    for st in chan_states(states, f):
        j = st.chan_of(f)
        if j is None:
            if code: res.append(st)
            continue
        if st.chans[j].connecting:
            if code: res.append(st)               # pending_err
            continue
        if code == 0:
            s2 = copy.deepcopy(st); s2.chans[j].shut = True; res.append(s2)
        elif st.chans[j].shut:
            res.append(st)                                                 # shut_err
        else:
            res += with_deliveries([st], j, lambda s: s.chans[j].broken)   # shut_err
    return res


def close_fd(s, f):
    j = s.chan_of(f)
    if j is not None:
        c = s.chans[j]; c.shut = c.closed = True; c.aborted = c.aborted or bool(c.inbox)
        s.open_fds = [(g, k) for (g, k) in s.open_fds if g != f]
    elif s.listener(f) is not None:
        for j in s.listener(f)[2]: s.reset(j, False)
        s.listeners = [x for x in s.listeners if x[0] != f]
    else:
        s.reserved.remove(f)


def check_close(states, conf, out):
    f = int.from_bytes(conf, "big"); code = out[0]
    res = []
    for st in states:
        if f not in st.used():
            if code == E["EBADF"]: res.append(st)
            continue
        if code == 0:
            s = copy.deepcopy(st); close_fd(s, f); res.append(s)
        else:                                             # close_intr: open or closed
            res.append(st); s = copy.deepcopy(st); close_fd(s, f); res.append(s)
            WARN.append("close interrupted (%d)" % code)
    return res


def check_listen(states, conf, out):
    port = int.from_bytes(conf, "big"); code, val = out[0], int.from_bytes(out[1:9], "big")
    res = []
    for st in states:
        if code:
            if 1 <= val <= 5: res.append(st)          # listen_fails: the world's choice
        elif st.fd_free() and val == st.lowest_fd():
            s = copy.deepcopy(st); s.listeners.append([val, port, []]); res.append(s)
    return res


def check_connect(states, conf, out):
    """l0_connect: value 0: no socket (transient, or EMFILE when no fd is
    below the limit); else the new fd (the lowest free) and connect_now's
    outcome: code 0 connected, EINPROGRESS pending, other: failed at once"""
    code, val = out[0], int.from_bytes(out[1:9], "big")
    res = []
    for st in states:
        if val == 0:
            if code == E["EMFILE"] and not st.fd_free():
                res.append(st)
            elif transient_ok(code):
                WARN.append("connect: no socket, error %d (transient)" % code); res.append(st)
            continue
        if not (st.fd_free() and val == st.lowest_fd()):
            continue
        s = copy.deepcopy(st); j = len(s.chans); c = Chan()
        if code == E["EINPROGRESS"]:
            c.connecting = True
        elif code != 0:
            c.broken = True
        s.chans.append(c); s.open_fds.insert(0, (val, j)); s.conn_chans.append(j)
        res.append(s)
    return res


def check_connerr(states, conf, out):
    """l0_connerr: the pending error (value 1), cleared; code 0: none"""
    f = int.from_bytes(conf, "big")
    code, val = out[0], int.from_bytes(out[1:9], "big")
    res = []
    for st in chan_states(states, f, (code,) if code and val == 1 else (E["ECONNREFUSED"],)):
        j = st.chan_of(f)
        if j is None:
            if code and val == 0: res.append(st)
            continue
        c = st.chans[j]
        if code == 0 and val == 0 and c.err is None:
            res.append(st)
        elif code and val == 1 and c.err == code:
            s = copy.deepcopy(st); s.chans[j].err = None; res.append(s)
    return res


def dedupe(states, cap=4096):
    seen, out = set(), []
    for s in states:
        k = s.key()
        if k not in seen:
            seen.add(k); out.append(s)
    if len(out) > cap:
        WARN.append("state cap %d reached: a later finding may be spurious" % cap)
    return out[:cap]


WARN = []
LAST_STATES = []

def check(log):
    """None if the run conforms, else (step, message); warnings in WARN"""
    del WARN[:]
    states = None
    reserved, fd_limit = None, None
    for i, ev in enumerate(log):
        try:
            if ev[0] == "reserved":
                reserved = ev[1]; continue
            if ev[0] == "fd_limit":
                if states is None:
                    fd_limit = ev[1]
                else:
                    for s in states: s.fd_limit = ev[1]
                continue
            if states is None:
                states = [State(reserved, fd_limit)]
            if ev[0] == "connect":
                for s in states: s.connects.append((ev[1], ev[2])); s.pending[ev[1]] = []
            elif ev[0] == "link":                         # peer ev[1] is the far end of
                for s in states:                          # the program's connect ev[2]
                    s.chan_of_client[ev[1]] = s.conn_chans[ev[2]]; s.pending[ev[1]] = []
            elif ev[0] == "data":
                for s in states: s.pending[ev[1]].append(("data", bytes.fromhex(ev[2]), False))
            elif ev[0] == "eof":
                for s in states: s.pending[ev[1]].append(("eof", None, False))
            elif ev[0] == "close":                        # FIN, or RST if it had unread data; RST later
                for s in states: s.pending[ev[1]] += [("eof", None, True), ("reset", None, True)]
            elif ev[0] == "rst":
                for s in states: s.pending[ev[1]].append(("reset", None, False))
            elif ev[0] in ("drain", "client_err", "note"):
                pass
            elif ev[0] == "fds":
                if not any(sorted(set(s.used())) == sorted(ev[1]) for s in states):
                    raise Inconsistent("the process's fds %s are not the model's" % ev[1])
            elif ev[0] == "call":
                _, name, conf, alen, out = ev
                conf, out = bytes.fromhex(conf), bytes.fromhex(out)
                prev = states
                states = {"listen": lambda: check_listen(states, conf, out),
                          "poll": lambda: check_poll(states, conf, out),
                          "accept": lambda: check_accept(states, conf, out),
                          "recv": lambda: check_recv(states, conf, out, alen),
                          "send": lambda: check_send(states, conf, out),
                          "shutdown": lambda: check_shutdown(states, conf, out),
                          "close": lambda: check_close(states, conf, out),
                          "connect": lambda: check_connect(states, conf, out),
                          "connerr": lambda: check_connerr(states, conf, out)}[name]()
                if not states:
                    # a transient failure has value 0 (the model's fail);
                    # connect's fd or connerr's 1 is never one
                    if (name not in ("poll", "close") and transient_ok(out[0]) and
                            int.from_bytes(out[1:9], "big") == 0):
                        WARN.append("step %d: %s error %d explained only as transient (POSIX 2.3)"
                                    % (i, name, out[0]))
                        states = prev
                    else:
                        raise Inconsistent("%s -> code %d value %d" % (
                            name, out[0], int.from_bytes(out[1:9], "big")))
                states = dedupe(states)
            global LAST_STATES
            LAST_STATES = states
        except Inconsistent as e:
            return (i, str(e))
    return None


if __name__ == "__main__":
    bad = 0
    for path in sys.argv[1:]:
        runs = json.load(open(path))
        for name, log in runs.items():
            r = check(log)
            print("%-28s %s" % (name, "conforms" if r is None else "FINDING at step %d: %s" % r))
            for w in WARN:
                print("    warning:", w)
            bad += r is not None
    sys.exit(1 if bad else 0)


def debug(log, upto):
    """The candidate states just before step upto (for reading findings)"""
    r = check(log[:upto])
    st = LAST_STATES
    for s in st:
        print("-- state: fds", s.open_fds, "clients->chan", s.chan_of_client)
        for j, c in enumerate(s.chans):
            print("   chan %d inbox=%d eof=%s err=%s broken=%s shut=%s closed=%s pending=%s" % (
                j, len(c.inbox), c.peer_eof, c.err, c.broken, c.shut, c.closed,
                [(k, o) for (k, _, o) in s.pending.get(client_of_chan(s, j), [])]))
