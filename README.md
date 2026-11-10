# qi-v2-platform-definition

The platform's formal definition in Lean 4, on Kahn process networks (Kahn, 1974). It defines and proves; it does not run. Every definition is checked by Lean, and every claim about the definitions is a theorem Lean proves, on Lean's standard axioms only. What each component does in code is its own project's; this is what that code must satisfy. What the project owns, gives and takes is `PRODUCTS.md`.

## What it defines

| File | Holds |
|---|---|
| `lean/Kahn/Domain.lean` | domains: partial orders with a least element in which every chain has a least upper bound; pairs and families of them |
| `lean/Kahn/Process.lean` | a process: a function meeting Kahn's condition (more input never takes back output; no output waits for the end of the input); composition, pairs, families; the least fixed point |
| `lean/Kahn/Network.lean` | a network: its equations and their least solution, which is again a process (Kahn's theorem) |
| `lean/Kahn/Log.lean` | a log: an append-only sequence of messages, finite or endless, ordered by prefix; every log is the limit of its finite prefixes |
| `lean/Kahn/Merge.lean` | no process merges two logs by arrival |
| `lean/Kafka.lean` | Kafka's topic: one log of records for each partition, everything ever appended to it; no view that replaces a record already given, as compaction and retention do, is a process |
| `lean/Acquisition.lean` | acquisition: a k-line contract's reader, cleaner and publisher, and the three kinds of data it publishes: the raw series (the vendor's corrected raw series, then its raw series), the clean series made from it, and the vendor's corrections; nothing published is taken back (`docs/acquisition.md` explains it) |
| `lean/Warehousing.lean` | warehousing: the warehouse consumer, one for each schema, on every partition |
| `lean/Visualization.lean` | visualization: a pure consumer of the clean topics and the engine's, giving the chart |
| `lean/MarketModelEngine.lean` | the market model engine (optional): a worker on the clean topics, publishing its own |
| `lean/Workspace.lean` | the working space: the four components wired by the topics, acquisition alone reading the input logs, the system one process of them; several working spaces side by side, each topic and each table with one writer |
| `lean/Wiring.lean` | the components as one working space, the engine optional, and what the whole system comes to |

The decisions behind the definitions, and those still open: `docs/decisions.md`.

## The product

`qi-v2-platform-definition` is a flake package of `lean/`, the Lake package `qi-v2-platform-definition`, as source, with this file and `LICENSE`, for a taker's Lake, on `x86_64-linux`. Its Lean is the one `lean/lean-toolchain` names, 4.35.0-rc3. It is not released yet; a release is a tag `qi-v2-platform-definition-<version>` (Changes, below), read over HTTPS with no login.

## Checking it

In the project's shell (`nix develop`), once: `make install`. Then `make lean` builds the definitions and checks every proof, and `make verify` runs every check a commit requires. `make help` lists the targets.

## Changes

None yet: 0.1.0 is not released.
