#!/usr/bin/env python3
"""CPU usage of echo servers: idle, under light load, and idle again.

For each server binary:
  1. idle-fresh:  started, no client has ever connected, PHASE seconds;
  2. light-load:  one client sends a 64-byte line every 100 ms and reads
                  the echo, PHASE seconds;
  3. idle-after:  that client has closed its connection, PHASE seconds.

CPU% of a phase = (process CPU time consumed in the phase) / (wall time
of the phase), from `ps -o cputime=` before and after (user + system, the
same figure `time` reports).  100% = one core busy.

The server is started without the connect-probe demo_clients.py uses
(that probe would itself leave a closed connection behind).

Not part of the trusted base: this only measures the servers.
"""
import argparse, os, socket, subprocess, time

LINE = b"x" * 63 + b"\n"


def cputime(pid):
    out = subprocess.run(["ps", "-o", "cputime=", "-p", str(pid)],
                         capture_output=True, text=True).stdout.strip()
    # [[dd-]hh:]mm:ss.ss
    days = 0
    if "-" in out:
        d, out = out.split("-", 1)
        days = int(d)
    parts = [float(x) for x in out.split(":")]
    secs = 0.0
    for x in parts:
        secs = secs * 60 + x
    return days * 86400 + secs


def phase(pid, seconds, work=None):
    c0, t0 = cputime(pid), time.time()
    if work:
        work(seconds)
    else:
        time.sleep(seconds)
    c1, t1 = cputime(pid), time.time()
    return 100.0 * (c1 - c0) / (t1 - t0)


def measure(binary, port, seconds):
    env = dict(os.environ, CAKE_ECHO_PORT=str(port))
    proc = subprocess.Popen([binary], env=env, stderr=subprocess.PIPE, text=True)
    proc.stderr.readline()            # "echo server: listening on ..."
    time.sleep(1.0)
    res = {}
    res["idle-fresh"] = phase(proc.pid, seconds)

    sock = socket.create_connection(("127.0.0.1", port))
    rtts = []

    def load(secs):
        end = time.time() + secs
        while time.time() < end:
            t = time.time()
            sock.sendall(LINE)
            got = b""
            while len(got) < len(LINE):
                got += sock.recv(len(LINE) - len(got))
            rtts.append(time.time() - t)
            time.sleep(max(0.0, 0.1 - (time.time() - t)))

    res["light-load"] = phase(proc.pid, seconds, load)
    sock.close()
    time.sleep(1.0)
    res["idle-after"] = phase(proc.pid, seconds)
    proc.terminate()
    proc.wait()
    rtts.sort()
    res["rtt-median-us"] = 1e6 * rtts[len(rtts) // 2]
    res["lines"] = len(rtts)
    return res


def main():
    p = argparse.ArgumentParser()
    p.add_argument("servers", nargs="+")
    p.add_argument("--seconds", type=float, default=30.0)
    p.add_argument("--port", type=int, default=7811)
    p.add_argument("--out")
    p.add_argument("--calibrate", help="a busy-polling binary: what busy polling costs here")
    a = p.parse_args()
    rows = []
    calib = ""
    if a.calibrate:
        proc = subprocess.Popen([a.calibrate])
        time.sleep(1.0)
        c = phase(proc.pid, a.seconds)
        proc.terminate()
        proc.wait()
        calib = (f"calibration: a C busy-polling loop (non-blocking polls) "
                 f"measures {c:.1f}% here\n")
        print(calib, flush=True)
    for i, b in enumerate(a.servers):
        r = measure(b, a.port + i, a.seconds)
        rows.append((os.path.basename(b), r))
        print(os.path.basename(b), r, flush=True)
    hdr = (f"phases of {a.seconds:.0f} s each; CPU% = process CPU time / wall time "
           f"(100% = one core)\n"
           f"{'server':22} {'idle-fresh':>11} {'light-load':>11} {'idle-after':>11} "
           f"{'rtt median':>11}\n")
    body = "".join(
        f"{n:22} {r['idle-fresh']:10.1f}% {r['light-load']:10.1f}% "
        f"{r['idle-after']:10.1f}% {r['rtt-median-us']:9.0f}us\n" for n, r in rows)
    print(calib + hdr + body)
    if a.out:
        with open(a.out, "w") as f:
            f.write(calib + hdr + body)


if __name__ == "__main__":
    main()
