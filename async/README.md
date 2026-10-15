# Verified asynchronous I/O for CakeML

This directory holds the design and a HOL4 model of monadic asynchronous
programming for CakeML, in the style of OCaml's Async/Lwt: `return`,
`bind`, `map`, `both` and `choose`, with loops such as an echo server. The
goal is to verify asynchronous CakeML programs, and the library and
scheduler they run on, against a model of the outside world.

## What is here

- `design/01-semantics.md`: the design note. It covers the model, the
  decisions and alternatives, the recursion rule, the world model, the
  refinement plan, the proposed main theorems, the risks and the open
  questions. Start here.
- `design/06-scheduler.md`: milestone M2, the scheduler and the
  no-busy-waiting theorem.
- `design/REVIEW-GUIDE.md`: a proposed short list of headline theorems,
  open decisions, and a reading order.
- `design/HANDOFF.md`: working notes for whoever continues the work
  (status, conventions, gotchas).
- `model/`: the HOL4 model. It depends only on HOL4, not on CakeML.

| File | Contents |
|---|---|
| `asyncCoreScript.sml` | snapshots and outcomes, response routing, guarded recursion (`fix`) |
| `asyncLevel1Script.sml` | Level 1: `wait`, `emit`, `return`, `bind`, `map`, `both`; monad laws; well-formedness |
| `asyncChooseScript.sml` | Async-style `choose`, which returns the loser still running, and the "nothing lost" theorem |
| `asyncLoopScript.sml` | the recursion rule: when a recursive definition is well-defined |
| `asyncEchoScript.sml` | the echo loop, and sanity checks evaluated on concrete histories |
| `asyncIdleScript.sml` | a loop that keeps its pending read across timeouts (the split recursion rule) |
| `asyncLevel2Script.sml` | Level 2: declared interest, erasure to Level 1, "no progress without a ready event" |
| `asyncLoop2Script.sml` | recursion at Level 2 |
| `asyncEcho2Script.sml` | the echo loop at Level 2: it erases to the Level 1 loop and is quiet |
| `asyncIdle2Script.sml` | the idle-deadline loop at Level 2: quiet, so a scheduler may block until the fd is readable or the timer fires |
| `asyncSchedScript.sml` | M2: the scheduler as a pure step function; tasks never lost; composition with the M1 semantics |
| `asyncSched2Script.sml` | M2: no busy-waiting: a scheduler that blocks through idle rounds behaves like one that polls every round |

In one sentence: a computation is a function from the history of world
snapshots it has been polled with to its action log and (optional) result.
Level 2 adds the set of events it is waiting for.

## Building

With HOL4 installed (the model was developed against HOL4 master 652d1f0aa
and Poly/ML 5.9.2):

```
cd async/model
Holmake
```

The build takes a few seconds and contains no `cheat`. Inside the CakeML
repository, Holmake also scans the repository's `holproject.toml`, which
adds a few seconds.

## Status

This is the M1 milestone: the core semantics, fully proved at both levels.
Highlights:

- monad and functor laws as exact equalities;
- `choose` loses nothing:
  `bind (choose m1 m2) rejoin = both m1 m2`;
- a recursion rule that admits the echo loop, which is proved well-formed;
- the Level 2 erasure theorems and quietness for every combinator,
  including `choose`;
- Level 2 recursion, and a quiet Level 2 echo loop that erases to the
  Level 1 one.

Conjectures and next steps are in `design/01-semantics.md` (§12, §16):

- M2: a scheduler as a pure step function;
- M3: CF-verified shell and FFI world model;
- M4: concurrent echo server.

Main theorems are marked in the scripts with `(* MAIN: ... *)`:

```
grep -n "MAIN:" async/model/*.sml
```
