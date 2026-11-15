# Opening

**Where it stands.** Milestones 1, 2 and 3 are done. Milestone 1: `lean/` holds the base (Kahn process networks, and sets of rows), Kafka's topic, the four components and their wiring; every file builds, its 51 theorems are proved, and `make lean` checks at every commit that no constant of `lean/` rests on any axiom but Lean's three (`dev/axioms.lean`). Milestone 2: 0.1.0, the tag `qi-v2-platform-definition-0.1.0`, is on `origin`. Milestone 3: the definition's open parts are exported, `export/parts.json`, one entry for every field of every structure of `lean/` (21 structures, 87 fields), made by Lean (`dev/parts.lean`, `make parts`) and checked at every commit by `make parts-check`, which `make verify` runs: the file is made again and compared byte for byte, and its form is checked (`dev/parts-check.py`); its form is `README.md`'s (The open parts), and the decision `docs/decisions.md`'s, the owner's of 2026-11-12. `qi-v2-platform-definition` 0.2.0 gives it in the package, `lean/` being 0.1.0's: the commit tagged `qi-v2-platform-definition-0.2.0`, which passes `make verify`; `nix build --offline .#qi-v2-platform-definition` builds the package, and its `export/parts.json` is the repository's. The market model engine's decision names the chanlun contract 4.0.0 (`c8b1e1e`). The export was reviewed by the other model, every entry against `lean/`; its three findings are settled (the form check checks the order and that no entry uses its own name; `README.md` says `doc` is trimmed and what refers to nothing).

**Open for the owner:**
- The push: `main`'s commits after `0b622b4` (the last `origin/main` this clone has seen) and the tag `qi-v2-platform-definition-0.2.0` are on this machine alone.
- `make locks-check` was not run (it reaches the network): whether `flake.lock`'s `qi-v2` and `kit` are today's is not known.
- What `uses` gives follows how Lean elaborates a type, by the rule as `README.md` gives it: `Wiring.cross_names` uses every field of `Kafka.Topic`, through the `match` of `Wiring.engineTopic`, where `Wiring.acq_names` uses `Kafka.Topic.name` alone. The rule is applied as written; whether it should read otherwise is the owner's.
- The list of `lean/`'s modules has three homes: `lean/lakefile.toml`, the imports of `dev/axioms.lean` and those of `dev/parts.lean`; one could hold it, the others checked against it.
- The kit's hook on `subagentStop` logged `ERROR ARGS_INVALID` for the role runs of the third review of milestone 1 (`agents.run/log`); it is settled in the kit's own project. Role runs by hand (`make run-start`, `make run-check`) write no line to `agents.run/log`: their check is `make run-check`'s output.

**The next task:** none is set: the three milestones are done, and the next is the owner's to set in `docs/milestones.md`.

## Standing rules learnt

None yet.
