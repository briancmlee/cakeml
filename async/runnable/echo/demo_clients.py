#!/usr/bin/env python3
"""Demo and measurement clients for the verified echo server.

demo:   start the server, connect three concurrent clients that each send
        lines (interleaved with the others) and check each one gets back
        exactly its own lines; write a timestamped transcript.
bench:  N clients x M lines, one line in flight per client; report
        throughput and round-trip latency.  --server can also be a
        baseline (e.g. "python3 demo_clients.py asyncio-server").
asyncio-server:  a trivial Python asyncio echo server, for comparison.

Not part of the trusted base: this only exercises the server.
"""
import argparse, asyncio, os, socket, statistics, subprocess, sys, threading, time


def start_server(cmd, port):
    env = dict(os.environ, CAKE_ECHO_PORT=str(port))
    proc = subprocess.Popen(cmd, shell=isinstance(cmd, str), env=env,
                            stderr=subprocess.PIPE, text=True)
    first = proc.stderr.readline().strip()        # "listening on ..."
    deadline = time.time() + 10
    while time.time() < deadline:                 # wait until it accepts
        try:
            socket.create_connection(("127.0.0.1", port), timeout=1).close()
            break
        except OSError:
            time.sleep(0.05)
    return proc, first


def recv_exactly(sock, n):
    buf = b""
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            raise EOFError("server closed the connection")
        buf += chunk
    return buf


def demo(args):
    proc, banner = start_server(args.server, args.port)
    log, lock, t0 = [], threading.Lock(), time.time()

    def note(who, what):
        with lock:
            log.append(f"[{time.time() - t0:7.3f}s] {who:8s} {what}")

    note("server", banner)
    ok = {}

    def client(name, lines, delay):
        s = socket.create_connection(("127.0.0.1", args.port))
        note(name, "connected")
        got_all = []
        for line in lines:
            data = (line + "\n").encode()
            s.sendall(data)
            note(name, f"sent     {line!r}")
            got = recv_exactly(s, len(data))
            note(name, f"received {got.decode().rstrip()!r}")
            got_all.append(got)
            time.sleep(delay)
        s.close()
        note(name, "closed")
        ok[name] = b"".join(got_all) == "".join(l + "\n" for l in lines).encode()

    clients = [
        ("alice", ["hello from alice", "alice: line 2", "alice: line 3"], 0.15),
        ("bob",   ["bob says hi", "bob: second line", "bob: third", "bob: fourth"], 0.1),
        ("carol", ["carol here", "carol: ünïcödé bytes ✓", "carol: last"], 0.12),
    ]
    threads = [threading.Thread(target=client, args=c) for c in clients]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    # after the others have gone: one more client (the server is still serving)
    client("dave", ["dave arrives after the others left"], 0)
    proc.terminate()
    proc.wait()
    note("server", "terminated (the server loop runs forever; stopped with SIGTERM)")
    for name in ok:
        note("check", f"{name}: received exactly its own lines: {ok[name]}")
    text = "\n".join(log) + "\n"
    print(text, end="")
    if args.log:
        with open(args.log, "w") as f:
            f.write(text)
    sys.exit(0 if all(ok.values()) else 1)


def bench(args):
    proc, banner = start_server(args.server, args.port)
    print(banner, file=sys.stderr)
    line = b"x" * (args.size - 1) + b"\n"
    lat, lock = [], threading.Lock()

    def client():
        s = socket.create_connection(("127.0.0.1", args.port))
        s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        mine = []
        for _ in range(args.lines):
            t = time.perf_counter()
            s.sendall(line)
            recv_exactly(s, len(line))
            mine.append(time.perf_counter() - t)
        s.close()
        with lock:
            lat.extend(mine)

    threads = [threading.Thread(target=client) for _ in range(args.clients)]
    t0 = time.perf_counter()
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    total = time.perf_counter() - t0
    proc.terminate()
    proc.wait()
    lat.sort()
    n = len(lat)
    print(f"{args.label}: {args.clients} clients x {args.lines} lines of {args.size} B: "
          f"{n / total:,.0f} lines/s, round trip median {statistics.median(lat) * 1e6:,.0f} us, "
          f"p99 {lat[int(n * 0.99) - 1] * 1e6:,.0f} us, max {lat[-1] * 1e6:,.0f} us")


def asyncio_server(args):
    port = int(os.environ.get("CAKE_ECHO_PORT", "7777"))

    async def handle(reader, writer):
        while True:
            data = await reader.read(4096)
            if not data:
                break
            writer.write(data)
            await writer.drain()
        writer.close()

    async def main():
        server = await asyncio.start_server(handle, "127.0.0.1", port)
        print(f"asyncio echo server: listening on 127.0.0.1:{port}", file=sys.stderr, flush=True)
        async with server:
            await server.serve_forever()

    asyncio.run(main())


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("mode", nargs="?", default="demo", choices=["demo", "bench", "asyncio-server"])
    p.add_argument("--server", default="build/echo_server")
    p.add_argument("--port", type=int, default=7777)
    p.add_argument("--log")
    p.add_argument("--clients", type=int, default=10)
    p.add_argument("--lines", type=int, default=1000)
    p.add_argument("--size", type=int, default=64)
    p.add_argument("--label", default="server")
    a = p.parse_args()
    {"demo": demo, "bench": bench, "asyncio-server": asyncio_server}[a.mode](a)
