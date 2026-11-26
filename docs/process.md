# How the project is worked: the machine, the files, the sessions

## The machine

Nix with flakes; GitHub's access for a push (an SSH key on the account). Then the clone, `nix develop`, `make install` (the kit at `dev/agents`, the pre-commit hook that runs `make verify`, then `make agents`). The shell gives every tool the targets call (`flake.nix`), Lean among them; make runs only in it, the hook's `make verify` among them, so a commit is made from it.

## The files, by kind

| Kind | Where | In git | Made by |
|---|---|---|---|
| the work | `lean/` (the definitions and their proofs) | yes | the sessions |
| the product, `qi-v2-platform-definition` | `flake.nix`'s package, `README.md` (with its Changes), `LICENSE`, `export/parts.json` (the definition's open parts) | yes | the sessions, a release by its tag; `export/parts.json` by `make parts` |
| the Lake package | `lean/lakefile.toml`, `lean/lake-manifest.json`, `lean/lean-toolchain` | yes | the sessions |
| what it owns, gives and takes | `PRODUCTS.md` | yes | the sessions, in the commit of the change it describes |
| the project's machinery | `flake.nix`, `flake.lock`, `Makefile`, `dev/no.credential/`, `dev/axioms.lean` (the axiom audit `make lean` runs), `dev/parts.lean` (the export `make parts` makes), `dev/parts.check.py` (the form `make parts-check` checks), `.envrc` | yes | the sessions |
| the state of the work | `docs/opening.md`, `docs/milestones.md`, `docs/designs/` (the designs a later session relies on, each with its reasoning and its model's parameters: `spec.md`, `acquisition.md`; `research/`, the research each component's spec rests on) | yes | each session, at its end |
| how an implementation is made from each definition: what it implements, the method, what is its own, how it is checked, how it takes the definition | `docs/guide/` (`market.md`, `chanlun.md`); `docs/acquisition.md`, acquisition's in words, until acquisition's guide takes its place | yes | the sessions, with the definition it guides |
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
| a model's parameters | the design they belong to, in `docs/designs/` |
| rules the owner gives in a session | the opening's Standing rules learnt, until approved for `agents/rules.md` |

## A session

1. **Start.** `git fetch https://github.com/zhifengzhang-sz/qi-v2-platform-definition main:refs/remotes/origin/main`, then `git merge --ff-only origin/main` (over HTTPS, `origin/main` kept: the SSH key is for a push only); `nix develop`; after a change of `flake.lock` or `agents/`, `make install`. Then `make locks-check`: each outdated lock reported to the owner with what updates it, none updated without the owner's say; where it stops for a credential (GitHub's compare, through gh's login), the owner is asked.
2. **Work.** The opening's one task. Before the first build of the session, the owner is asked. Checks run in the role `checker` (`make lean`, `parts-check`, `products-check`, `agents-check`, `verify`). No fallbacks.
3. **End.** `docs/opening.md` rewritten for the next session, `docs/milestones.md` brought up to date; staged by explicit paths, so that the work tree is what is staged; checked by `make verify`; committed, the hook running `make verify` again; and pushed.
