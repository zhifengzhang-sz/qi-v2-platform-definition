# Opening

**Where it stands.** Milestone 1 is drafted, committed and pushed. `lean/` holds the base (Kahn process networks), Kafka's topic, the four components and their wiring; every file builds, and its 47 theorems are proved on Lean's standard axioms. The other model reviewed an earlier draft once: the base is sound, and its seven points are decided and in the Lean (`docs/decisions.md`), with corrections added as revisions and resets (a reset a replay by acquisition's second reader), the topics' kinds, acquisition alone reading the input logs, one acquisition to a working space and several working spaces side by side, and one writer for each topic and each table. The project follows `qi-v2-nix`'s `practices.md`: the flake, the Makefile, `PRODUCTS.md`, `agents/`, `docs/`.

**Open for the owner:**
- What a reader of a clean topic (the engine, visualization) does at a reset (`docs/decisions.md`, Open), with the proposal; perhaps the implementation's, as the replay's switch is.
- `flake.lock`'s nixpkgs is outdated (`make locks-check`: locked `fa1373130d`, `nixos-26.05` at `ac588ef1c9`); it comes through qi-v2, so it is updated in qi-v2's lock, then `nix flake update qi-v2`.

**The next task:** a second review by the other model of `lean/` and `docs/acquisition.md`, in the role `reviewer`, its findings settled. The files it needs: `lean/`, `docs/acquisition.md`, `docs/decisions.md`.

## Standing rules learnt

None yet.
