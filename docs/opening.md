# Opening

**Where it stands.** Milestones 1, 2 and 3 are done (`docs/milestones.md`): `lean/` holds the base, Kafka's topic, the four components and their wiring, on Lean's three axioms (`make lean`, `dev/axioms.lean`); 0.1.0 is on `origin`; 0.2.0, the commit tagged `qi-v2-platform-definition-0.2.0`, gives the export of the definition's open parts, `export/parts.json`, checked by `make parts-check`. Milestone 4: `docs/designs/spec.md` is the spec of the contract specs and the component specs, a statement of what each part is, its history in `git`; `docs/decisions.md` holds the owner's decisions, and apart, at its end, the session's choices the spec is written on, made with the owner and waiting on no one. The Lean holds the spec but for the component specs: market's and chanlun's records and rules, identical to `qi-v2-contracts`' Lean at `market-2.0.1` and `chanlun-4.0.1` (commit `6c9e4dc`) but for the reader of Protobuf's JSON, with each record's `Keeps` (`KLine.Keeps`, …, exactly when it breaks none of its rules) and each field's doc comment; the components taking them; each topic named by the naming (`Wiring.Naming`) from the series' signature (`Acquisition.Signature`, a field of the wiring) and its kind, with one partition, no key and its kind's message (`Kafka.Topic.ofName`); one topic of each kind, the engine and visualization reading one topic each; `Workspaces` of one naming, no two of one signature, so that no two topics of any of them have one name (`Workspaces.topics_distinct`, a theorem). 16 modules, 65 theorems, 1059 constants, on Lean's three axioms; the export 140 entries, its types still open Kafka's general topic's key and value, warehousing's topics, which the wiring fills, and the general working space's.

**For the owner, choices to make together (`docs/decisions.md`, The session's choices):**
- The cleaner's rule: it keeps a k-line whose date is after every kept one's, so after a k-line dated far in the future it drops every k-line until one's date passes it. The other ways: give a k-line only once the next one's date passes it, each then a k-line late; or drop a k-line whose date is past a bound the series' period gives.
- The engine's result message, one of chanlun's six records by its case; the other way, one message for each k-line read.
- Market's `OngoingKLine` carried by no topic, so the chart shows no bar still going on.

**For the owner, besides:**
- The export does not show the engine's message: `MarketModelEngine.Result` is an inductive, which by `README.md`'s rule (The open parts) has no entry and refers to nothing. Whether the rule follows an inductive's constructors is the owner's.
- The export's `version` is flake.nix's, 0.2.0, on 133 entries, where the release 0.2.0's had 87: it moves with the release.
- Where the `.proto` of the engine's result message is kept: it is the platform's message, not a contract's, and not the definition's.
- The push: `main`'s commits after `0b622b4` (the last `origin/main` this clone has seen) and the tag `qi-v2-platform-definition-0.2.0` are on this machine alone.
- `make locks-check` was not run (it reaches the network): whether `flake.lock`'s `qi-v2` and `kit` are today's is not known; both are pinned at `27e7c47`.
- What `uses` gives follows how Lean elaborates a type, by the rule as `README.md` gives it: an entry whose topic is made by `Kafka.Topic.ofName` uses every field of `Kafka.Topic`, `Key` and `Value` among them, which that topic fixes (`Wiring.warehousing`). The rule is applied as written.
- The list of `lean/`'s modules has three homes: `lean/lakefile.toml`, the imports of `dev/axioms.lean` and those of `dev/parts.lean`; one could hold it, the others checked against it.
- Role runs by hand (`make run-start`, `make run-check`) write no line to `agents.run/log`: their check is `make run-check`'s output.

**The next task:** a session that did not write it reviews task 2 as it now stands (`06752a0..` the commit that brings this opening): the contract specs in the Lean and the topics as the spec gives them. Then the component specs in the Lean, task 3 (`docs/milestones.md`, milestone 4): each component's spec, a structure of `Prop`s, one for each requirement, the theorems the spec names (The working space), and the export made again. Its files: `docs/designs/spec.md`; `docs/decisions.md`; `lean/Kahn/Log.lean` (`Log.filterMap`), `lean/Acquisition.lean`, `lean/Warehousing.lean`, `lean/Visualization.lean`, `lean/MarketModelEngine.lean`, `lean/Wiring.lean`; `export/parts.json`; `README.md`, `docs/acquisition.md`.

## Standing rules learnt

- This project reads any project's folder, writing none of it, but one, which the owner's brief of 2026-11-19 names and this project does not read (the owner, 2026-11-19).
- A fault the session made is fixed by the session without waiting for the owner's word: the owner's one decision on a fault is that the right thing is delivered. Design choices are made with the owner (the owner, 2026-11-20).
- A file's name has no `-` or `_`: a `.` takes their place (the owner, 2026-11-20). Names a tool fixes are kept: `lean/lean-toolchain`, `lean/lake-manifest.json`, `dev/hooks/pre-commit`.
