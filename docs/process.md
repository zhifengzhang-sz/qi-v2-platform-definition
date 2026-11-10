# How the project is worked: the machine, the files, the sessions

## The machine

Nix with flakes; GitHub's access for a push (an SSH key on the account). Then the clone, `nix develop`, `make install`. The shell gives every tool the targets call (`flake.nix`), Lean among them.

## The files, by kind

| Kind | Where | In git | Made by |
|---|---|---|---|
| the work | `lean/` (the definitions and their proofs) | yes | the sessions |
| the product, `qi-v2-platform-definition` | `flake.nix`'s package, `README.md` (with its Changes), `LICENSE` | yes | the sessions, a release by its tag |
| the Lake package | `lean/lakefile.toml`, `lean/lake-manifest.json`, `lean/lean-toolchain` | yes | the sessions |
| what it owns, gives and takes | `PRODUCTS.md` | yes | the sessions, in the commit of the change it describes |
| the project's machinery | `flake.nix`, `flake.lock`, `Makefile`, `dev/hooks/`, `dev/no-credential/`, `dev/axioms.lean` (the axiom audit `make lean` runs), `.envrc` | yes | the sessions |
| the state of the work | `docs/opening.md`, `docs/milestones.md`, `docs/decisions.md`, `docs/designs/` (none yet) | yes | each session, at its end |
| what a definition means, in words | `docs/acquisition.md` | yes | the sessions, with the definition it explains |
| the rules for agents, their source | `agents/` | yes | the sessions, the owner approving |
| the rules for agents, generated | `AGENTS.md`, `CLAUDE.md`, `.claude/agents/`, `.claude/workflows/`, `.github/agents/`, `.github/hooks/kit.json`, `agents.generated`; a run's record, `agents.run/`; the developer's own `agents.local.json` | no | `make agents` and `make run-start`, by the kit |
| the tools, the kit | `/nix/store`, pinned by `flake.lock`; `dev/agents` | the pins | `nix develop`, `make install` |
| build output and reports | `lean/.lake/`, `.reports/` | no | the targets |
| the owner's notes | `todo.md` | no | the owner |

## Where each rule lives

| Rules | Home |
|---|---|
| the standing rules, for every agent and the session | `agents/rules.md` (its generated copy `AGENTS.md`) |
| each role's | `agents/roles/<role>.md` |
| the decisions | `docs/decisions.md` |
| rules the owner gives in a session | the opening's Standing rules learnt, until approved for `agents/rules.md` |

## A session

1. **Start.** `git fetch https://github.com/zhifengzhang-sz/qi-v2-platform-definition main:refs/remotes/origin/main`, then `git merge --ff-only origin/main` (over HTTPS, `origin/main` kept: the SSH key is for a push only); `nix develop`; after a change of `flake.lock` or `agents/`, `make install`. Then `make locks-check`: each outdated lock reported to the owner with what updates it, none updated without the owner's say; where it stops for a credential (GitHub's compare, through gh's login), the owner is asked.
2. **Work.** The opening's one task. Before the first build of the session, the owner is asked. Checks run in the role `checker` (`make lean`, `products-check`, `agents-check`, `verify`). No fallbacks.
3. **End.** `docs/opening.md` rewritten for the next session, `docs/milestones.md` brought up to date; committed by explicit paths after the checks pass, and pushed.
