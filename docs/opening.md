# Opening

## Where it stands

- Milestones 1 to 3 are done (`docs/milestones.md`). 0.1.0 and 0.2.0 are released, on `origin` with their tags.
- Milestone 4, the contract specs and the component specs, is in progress. In the Lean: the base, Kafka's topic, the four components and their wiring, and market's and chanlun's contracts (on `main`, in no release yet). No component's spec is in the Lean yet.
- Acquisition's design is being worked out from the vendor's stream: `docs/designs/acquisition.md`, with its evidence in `docs/designs/research/stream.md`. It sets the stream's axioms, taken from Kafka as the model of a stream, against the stream the vendor provides. The vendor's stream holds none of them. The raw topic is the log of the vendor's statements, each bar as the vendor gave it with the time it was read, and watermarks. The clean series, the refused bars, the corrections and the bar still forming are computed from it by one settling rule, with a delay `d`.
- `lean/CleanStream.lean`, with no Kafka in it: the clean k-line stream (`Valid`); the vendor's feed, a statement read before its window began no word of the vendor's (`Statement.begun`), and its features on a sample feed; the clean data of a feed (`CleanOf`), one at most (`CleanOf.unique`); no process gives it (`no_process`, `no_process_raw`), a process giving only last words gives nothing (`final_gives_nothing`), and none is both live and final (`no_live_final`). Route 1: the clean data made outside the stream by a function that is no process (`construct`, `cleanOf_construct`, `construct_not_process`), passed in by acquisition (`store_route`). Route 2: the settling rule on the raw topic (`settle`, `settleP`, on `lean/Kahn/Prefix.lean`), always a clean k-line stream (`settleP_valid`), at each moment the clean data of the windows settled so far (`settle_settled`), the clean data on a raw topic on time (`settle_clean`), the same as route 1 there (`settle_eq_construct`), and giving whatever any correct rule gives, at the same place (`settle_earliest`). Reviewed by the reviewer on Fable 5.2, its findings fixed and rechecked once, the recheck's new findings fixed by the session. Built, the axiom audit passed, the export made again.
- `docs/designs/spec.md` and the rest of the Lean do not yet follow acquisition's design.
- The project keeps no decision log. A design lives in `docs/designs/` with its reasoning; what is chosen is a model's parameters, stated in its design (`agents/rules.md`).

## How the work goes

- From the axioms and each component's objectives down. An objective is what the component makes true of what it publishes. Its requirements are `Prop`s, and a theorem shows that they give the objective. Objectives and features are stated formally, as `Prop`s and theorems, not as comments.
- The owner sets the foundation: the axioms and the objectives. The session works out what follows from the model, writes it in the design with its reasoning, and shows it.
- One component at a time: acquisition first, then warehousing, the engine and visualization.

## The next task

Acquisition's spec, joining the new module to the rest of the Lean: `lean/Acquisition.lean` and `lean/Wiring.lean` still hold the earlier design, on Kafka's topic; acquisition's objectives, requirements and features stated from `lean/CleanStream.lean`, which route or routes it takes; the corrections and the refused bars as topics computed from the raw topic; `docs/designs/spec.md` brought to it. Then the other components the same way, the workflow, and the release 0.3.0. `docs/designs/research/stream.md`, written by the researcher on Fable 5.2, has not had its review by another model.

Its files: `lean/CleanStream.lean`, `lean/Acquisition.lean`, `lean/Wiring.lean`, `lean/Kafka.lean`, `docs/designs/acquisition.md`, `docs/designs/spec.md`.

## Open for the owner

- The push of `1783ffb` failed for the SSH key's passphrase, which this shell cannot ask for: `git push origin main` from the owner's shell.
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
