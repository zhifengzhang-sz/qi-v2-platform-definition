# Opening

## Where it stands

- Milestones 1 to 3 are done (`docs/milestones.md`). 0.1.0 and 0.2.0 are released, on `origin` with their tags.
- Milestone 4, the contract specs and the component specs, is in progress. In the Lean: the base, Kafka's topic, the four components and their wiring, and market's and chanlun's contracts (on `main`, in no release yet). No component's spec is in the Lean yet.
- Acquisition's design is being worked out from the vendor's stream: `docs/designs/acquisition.md`, with its evidence in `docs/designs/research/stream.md`. It sets the stream's axioms, taken from Kafka as the model of a stream, against the stream the vendor provides. The vendor's stream holds none of them. The raw topic is the log of the vendor's statements, each bar as the vendor gave it with the time it was read, and watermarks. The clean series, the refused bars, the corrections and the bar still forming are computed from it by one settling rule, with a delay `d`.
- `lean/CleanStream.lean`, with no Kafka in it: the clean k-line stream (`CleanStream.Valid`); the vendor's feed and its features, each shown on a sample feed; the clean data of a feed (`CleanOf`); the proof that no process gives the clean data of every feed (`no_process`); and its corollary's first route, the clean data made outside the stream from a snapshot (`construct`, `cleanOf_construct`) and fed by acquisition, which cleans nothing (`feed`, `store_route`). Built, the axiom audit passed (17 modules, 1206 constants), the export made again (155 entries); the reviewer's round runs once route 2 is done. The two routes: `docs/designs/acquisition.md`.
- `docs/designs/spec.md` and the rest of the Lean do not yet follow acquisition's design.
- The project keeps no decision log. A design lives in `docs/designs/` with its reasoning; what is chosen is a model's parameters, stated in its design (`agents/rules.md`).

## How the work goes

- From the axioms and each component's objectives down. An objective is what the component makes true of what it publishes. Its requirements are `Prop`s, and a theorem shows that they give the objective. Objectives and features are stated formally, as `Prop`s and theorems, not as comments.
- The owner sets the foundation: the axioms and the objectives. The session works out what follows from the model, writes it in the design with its reasoning, and shows it.
- One component at a time: acquisition first, then warehousing, the engine and visualization.

## The next task

Route 2 in the Lean (`docs/designs/acquisition.md`, Route 2): the raw topic's records, a statement with its time of reading and a watermark; the settling rule as a process, with the theorems that it gives a valid clean k-line stream and that it gives the clean data exactly when the vendor revises no window after it settles. Then one review round of both routes (`lean/CleanStream.lean`, `docs/designs/acquisition.md`, `docs/designs/research/stream.md`) and the checker's `make verify`. Then acquisition's spec, `docs/designs/spec.md` brought to it, and the other components the same way.

Its files: `lean/CleanStream.lean`, `docs/designs/acquisition.md`, `docs/designs/research/stream.md`, `lean/Kahn/Log.lean`, `lean/Kahn/Process.lean`, `lean/Contract/Market.lean`.

## Open for the owner

- `make locks-check` (2026-11-23): `qi-v2` is outdated, at 1.0.2 where 1.1.0 is released, and `nixpkgs` with it. `nix flake update qi-v2` updates both; not run without the owner's say.
- The kit's shared rules still ask every project for a `docs/decisions.md`; this project keeps none. Changing the shared rule is the kit's.
- Whether the vendor sends a per-minute bar before its minute ends: only watching its stream settles it, which needs the owner's subscription.
- This project's release: by its tag (`README.md`) or by a release branch, `release/qi-v2-platform-definition`, as the kit's shared rule has it; `origin` has no such branch.
- The researcher saves the PDFs it reads in the session's scratchpad, where its role has it run only what reads.

## Also open

- Each research file's "What it gives the spec" lists the questions each component's design has to answer (`docs/designs/research/`).
- The export does not show the engine's message: `MarketModelEngine.Result` is an inductive, which by `README.md`'s rule (The open parts) has no entry.
- Where the `.proto` of the engine's result message is kept: it is the platform's message, not a contract's.
- The list of `lean/`'s modules has three homes: `lean/lakefile.toml`, and the imports of `dev/axioms.lean` and `dev/parts.lean`.

## Standing rules learnt

- This project reads any project's folder, writing none of it, but one, which this project does not read, as it could mislead. Formal specs of earlier iterations are in other projects, and are read where the definition needs them.
- Research from other projects is taken in as content, with its original sources, never citing or naming a project.
- A fault the session made is fixed by the session without waiting.
- This project gives all the formal specs the rest of the building needs; how another project works is not its concern.
- Verification, the reviewer's round and the checker's `make verify`, runs once, at the end of a piece of work.
- Answers and documents are in plain English, in short sentences. Nothing is attributed to the owner, and no design is called a decision.
- A file's name has no `-` or `_`: a `.` takes their place. Names a tool fixes are kept: `lean/lean-toolchain`, `lean/lake-manifest.json`.
