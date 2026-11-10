# Milestones

## 1. The platform's formal definition

**What.** The platform defined in Lean on Kahn process networks: the base (logs, processes, networks), Kafka's topic, the four components (acquisition, warehousing, visualization, the market model engine) and their wiring, every claim proved from the base up, so that the platform's projects can be rebuilt on it.

**Stands.** Drafted: every file of `lean/` builds, and its 45 theorems are proved on Lean's standard axioms. It was reviewed three times: an earlier draft by the other model (the base found sound, its wording fixed, its seven points decided and in the Lean), then `lean/` by reading (the base sound, no theorem's statement weaker than its comment), after which acquisition was made simpler: three kinds of data, no corrected raw series, no reset in the working space (`docs/decisions.md`); then `lean/`, the docs and the package by the other model, each finding checked against the sources. Findings of the second and third reviews are still open (`docs/opening.md`). The axioms were checked once, by a file outside the project: no constant of `lean/` rests on any axiom but Lean's three; `make lean` does not check it yet.

## 2. The first release

**What.** The product `qi-v2-platform-definition` 0.1.0, tagged `qi-v2-platform-definition-0.1.0`, so that a project pins the tag over HTTPS with no login.

**Stands.** Not started; it follows milestone 1.
