# The rules of qi-v2-platform-definition's work

qi-v2-platform-definition: the platform's formal definition in Lean, on Kahn process networks, under `lean/` (`README.md`). These are its standing rules, for an agent of any kind; the format of this file is the kit's (`agents/README.md`).

## The session

**Read first.**

1. `docs/opening.md`: where the last session stopped, what is open for the owner, the next task, and the files that task needs. Read those files, and no others, before starting.
2. `docs/milestones.md`: what the work is for.
3. `docs/process.md`: how a session starts and ends, and where each rule lives.

Read the others only when the task touches them: `docs/decisions.md` before changing what a definition says; `PRODUCTS.md` before a change to what the project gives or takes.

**The rules.**

- **The owner's local file**: `todo.md`, never committed.
- **The repository.** This folder is on `main`; its remote is `origin`, `zhifengzhang-sz/qi-v2-platform-definition` on GitHub, public; pushed after a commit.
- **What it takes, and from where**: the tools, Lean among them, from the flake. No file of another project is reached by a path.
- **The credentials.** No credential of the owner's is used without asking first, whatever the reason, GitHub's rate limit included: gh's token, a registry login, a token passed to `nix` through `NIX_CONFIG` or the environment, the GitHub tools of an MCP server (they hold the owner's token), an SSH key for anything but a push the brief allows (a `git fetch` or `git ls-remote` of `origin` uses it too). GitHub's public repositories are read over HTTPS.

## Every role

- **Public.** The project is public: it takes nothing that cannot be read with no login, and names no private project in any file.
- **A definition is a definition.** The Lean defines and proves; it is not code to run, and it is `noncomputable` where the limit of logs needs it. What a component does in code is its own project's.
- **Every claim is proved.** A comment says what its definition or theorem says, no more; a statement that is a modelling choice, not a theorem, says so. A proof rests on Lean's standard axioms only: no `sorry`, no axiom of the project's own.
- **Markdown prose** has each paragraph and each list item on one line.
- **The project's secrets**: none.
