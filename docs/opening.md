# Opening

**Where it stands.** Milestone 1 is drafted, committed and pushed. `lean/` holds the base (Kahn process networks), Kafka's topic, the four components and their wiring; every file builds, and its 45 theorems are proved on Lean's standard axioms. It was reviewed twice. The second review, of `lean/` by reading alone, found the base sound and no theorem's statement weaker than its comment. Its findings on acquisition (a corrected raw series and a reset each put two logs into one by arrival, which no process does; the reset's reader had no wire from the cleaner; the history as acquisition's own topics could not be wired) are settled by a simpler design, decided and in the Lean (`docs/decisions.md`): three kinds of data (raw, clean, corrections), no corrected raw series, the clean series made from the raw series, the raw series the vendor's corrected raw series and then its raw series, the reader reading both parts, how (a replayer in it, say) the implementation's, a reset outside the working space.

**Open for the owner:**
- The review's findings not yet settled:
  1. One writer for each table holds for working spaces, not for logs: `Workspaces.tables_distinct` gives one working space to a table, and within one `Wiring.workspace` pushes the log of every partition of a topic into the same table (`table o := S.table o.1`), and `Wiring.table` may send several topics there. By the reason given for one writer (`Kahn.no_arrival_merge`) that is a merge by arrival at the table, unless a table is unordered, which the definition does not say.
  2. A publisher is any process, one that publishes nothing among them: the definition says what the topics of a kind are made from, not that they hold it.
  3. Wording: `lean/Workspace.lean`'s header says what each component reads and writes is defined in its own project, and `lean/Wiring.lean` defines it; `lean/Kahn/Merge.lean`, `lean/Visualization.lean` and `lean/MarketModelEngine.lean` say a process can merge by content, and no definition or theorem shows one; `lean/MarketModelEngine.lean` says the engine's messages derive from the chanlun contract 3.1.0, which nothing in the definition carries (whether that contract is public was not checked); `lean/Kahn/Network.lean` says "run in any order", and Kahn's result needs a fair order; `lean/Kahn/Domain.lean` says Mathlib's `OmegaCompletePartialOrder` is the same notion, and it has no least element; `docs/acquisition.md` says the clock has to be one of the reader's input logs, and as a second log it would be merged by arrival: its ticks have to be records of the source.
- Not checked: the axioms each theorem rests on (`#print axioms` was not run; the source has no `sorry`, `axiom` or `native_decide`, and `make lean` looks for `sorry` alone).

**The next task:** the findings above settled, the first of them with the owner: what a table is, and whether one writer for a table means one working space or one log. The files it needs: `lean/Workspace.lean`, `lean/Wiring.lean`, `lean/Warehousing.lean`, `docs/decisions.md`.

## Standing rules learnt

None yet.
