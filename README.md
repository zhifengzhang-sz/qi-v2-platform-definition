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
| `lean/Kahn/Rows.lean` | a set of rows: messages in no order; several logs into one set of rows is a process |
| `lean/Contract/Market.lean` | market's contract, its formal definition: its records, the K-line and the ongoing K-line, field for field its `.proto`'s messages, each field saying what it is; its rules, each a name and what holds of a record that keeps it; and what it is for a record to keep its contract (`KLine.Keeps`, …), exactly when it breaks none of its rules |
| `lean/Contract/Chanlun.lean` | 缠论's contract, its formal definition: its records, the merged bar, the 分型, the line, the 线段, the 走势 and the 中枢, each field saying what it is; its rules, each of one record alone; and what it is for a record to keep its contract (`MergedBar.Keeps`, …) |
| `lean/Kafka.lean` | Kafka's topic: one log of records for each partition, everything ever appended to it; no view that replaces a record already given, as compaction and retention do, is a process; a topic of a working space, named, with one partition, no key and values of a given type |
| `lean/Acquisition.lean` | acquisition, of market's k-line: its reader, cleaner and publisher, and the three kinds of data it publishes, each on a topic of its own: the raw series (the vendor's corrected raw series, then its raw series), the clean series made from it, and the vendor's corrections; nothing published is taken back; a series' signature (`docs/acquisition.md` explains it) |
| `lean/Warehousing.lean` | warehousing: the warehouse consumer, one for each schema, on every partition, what it pushes for a topic of the type of its values |
| `lean/Visualization.lean` | visualization: a pure consumer of the clean topic and the engine's, giving one log for each, of the type of its values, from which the chart is drawn |
| `lean/MarketModelEngine.lean` | the market model engine (optional): a worker on one clean topic, its series, publishing its own, of its results, each one of chanlun's records |
| `lean/Workspace.lean` | the working space: the four components wired by the topics, acquisition alone reading the input logs, the system one process of them; a table of the database the rows pushed into it, in no order |
| `lean/Wiring.lean` | the components as one working space, of one series, the engine optional: each topic named by the naming from the series' signature and its kind, no two of one name; every message a contract's record or made of them; what the whole system comes to; several working spaces side by side, each one a wiring makes, of one naming, no two of one signature |

The decisions behind the definitions, and those still open: `docs/decisions.md`.

## The product

`qi-v2-platform-definition` is a flake package of `lean/`, the Lake package `qi-v2-platform-definition`, as source, with this file, `LICENSE` and `export/parts.json`, the definition's open parts (below), for a taker's Lake, on `x86_64-linux`. In the package the files of `lean/` are at its root, beside this file, `LICENSE` and `export/parts.json`, and nothing else of the repository is there: the other paths this file and the Lean's comments name (`docs/`, `PRODUCTS.md`, `dev/`, the make targets) are the repository's. Its Lean is the one `lean/lean-toolchain` names, 4.35.0-rc3. Its release is 0.2.0, the tag `qi-v2-platform-definition-0.2.0`; a release is a tag `qi-v2-platform-definition-<version>` (Changes, below), read over HTTPS with no login.

## The open parts

`export/parts.json` gives the definition's open parts, so that what each product of the platform must give is read from the definition itself. Lean makes it from the definition, by `dev/parts.lean` (Checking it, below). It is a JSON object: `version`, the release's version, and `parts`, one entry for every field of every structure `lean/` declares, classes among them; a structure's fields are its own, a parent's (`Kahn.Domain.toPoset`) among them. The entries are sorted by name, and each has:

- `name`: the field's full Lean name (`Acquisition.Data.Topic`).
- `structure`: the structure it is a field of (`Acquisition.Data`).
- `type`: its type as Lean prints it in its structure, as `#print` shows it: the structure's parameters and `self` free, on one line, a proof printed `⋯`.
- `doc`: its doc comment, as Lean holds it with the spaces at its ends trimmed, or empty.
- `uses`: the other parts its type refers to, sorted: a projection of a structure of `lean/` is its field; such a structure, or its constructor, is each of its fields; a definition of `lean/` (an abbreviation, an instance, a `match` helper) refers to what it comes to, unfolded where it is used, its value applied to the arguments it is given; any other constant (a theorem, an inductive type of `lean/` that is not a structure, with its constructors and recursors, or a constant from outside `lean/`) refers to nothing, and the terms it is applied to are read on. Every name in `uses` is the name of an entry.

## Checking it

In the project's shell (`nix develop`), once: `make install`. Then `make lean` builds the definitions, checks every proof, and checks that no constant of `lean/` rests on an axiom other than Lean's three (`dev/axioms.lean`), and `make verify` runs every check a commit requires. `make parts` makes `export/parts.json` from `lean/` as built, and `make parts-check`, which `make verify` runs, checks that the file is what Lean gives and that it holds to its form (`dev/parts.check.py`). `make help` lists the targets.

## Changes

- **0.2.0**: the definition's open parts, `export/parts.json` (The open parts), made by Lean from the definition and given in the package; the definition is 0.1.0's.
- **0.1.0**: the first release. The base (Kahn process networks: domains, processes, networks, logs, sets of rows), Kafka's topic, the four components (acquisition, warehousing, visualization, the market model engine) and their wiring; 51 theorems, each proved on Lean's standard axioms only; Lean 4.35.0-rc3.
