# qi-v2-platform-definition (README.md): make targets, run inside `nix develop` (flake.nix, docs/process.md), which
# gives every tool they call (flake.nix's shell), and the kit at dev/agents (make install); of the host, only nix.
# Outside it, make stops, the pre-commit hook's make verify among them.
ifneq ($(QI_DEFINITION_SHELL),1)
$(error run make inside this project's shell: nix develop, then make …, or nix develop -c make …; a commit from nix develop (docs/process.md))
endif
SHELL := $(shell command -v bash)
ifeq ($(SHELL),)
$(error no bash in this project's shell)
endif

PY := python3

.PHONY: help agents-check lean parts parts-check

help: ## the targets
	@grep -E '^[a-z-]+:.*##' $(MAKEFILE_LIST) | sed 's/:.*## /\t/' | expand -t 22

# ---------------------------------------------------------------- the kit's part, as qi-v2-nix's practices.md gives it (section 8)

# verify then runs the project's own checks, and locks-check runs the kit with no credential of the owner's (below).

# the kit at the commit flake.lock names (section 1), read by nix when make install needs it
KIT = $(shell nix eval --raw --impure --expr 'let l = builtins.fromJSON (builtins.readFile ./flake.lock); k = l.nodes.$${l.nodes.$${l.root}.inputs.kit}.locked; in "github:$${k.owner}/$${k.repo}/$${k.rev}?dir=$${k.dir}"')
NEEDKIT = @test -x dev/agents/bin/kit || { echo "$@: no kit at dev/agents: make install"; exit 1; }
# the kit for the checks: the one make install linked, else run from KIT (CI, or a machine before make install)
KITRUN = $(if $(wildcard dev/agents/bin/kit),dev/agents/bin/kit,nix run "$(KIT)" --)

.PHONY: install agents run-start run-check locks-check products-check verify

install: ## the kit at dev/agents, the pre-commit hook that runs make verify, then make agents
	mkdir -p dev && nix build "$(KIT)" -o dev/agents
	hook=$$(git rev-parse --git-path hooks/pre-commit) && printf '#!/bin/sh\nexec make verify\n' > "$$hook" && chmod +x "$$hook"
	$(MAKE) agents

agents: ## each kind's files from agents/ (kit generate)
	$(NEEDKIT)
	dev/agents/bin/kit generate

run-start: ## before a role's run, ROLE=<role> (kit run-start)
	$(NEEDKIT)
	dev/agents/bin/kit run-start --role "$(ROLE)"

run-check: ## after it, ROLE=<role>, FILES=<a,b> for a role that writes them (kit run-check)
	$(NEEDKIT)
	dev/agents/bin/kit run-check --role "$(ROLE)" $(if $(FILES),--files "$(FILES)")

# kit locks asks each input's source over HTTPS; for a folder input whose repository moved it asks GitHub's compare
# through gh, and where HTTPS fails it asks again by SSH. Both would act with a credential of the owner's, so it runs
# with neither: dev/no.credential's gh, which never runs, first on PATH, and git with no SSH. Where it needs one, it
# stops, naming it, and the owner is asked (agents/rules.md, The credentials). The project has no locks of its own:
# lean/lake-manifest.json has no package.
locks-check: ## whether each lock's source has moved past it (kit locks; then the project's own locks)
	PATH="$(CURDIR)/dev/no.credential:$$PATH" GIT_SSH_COMMAND=false $(KITRUN) locks --root .

products-check: ## whether PRODUCTS.md states what the project has (kit products)
	$(KITRUN) products --root .

# The project's own part of verify, after the kit's: make verify checks the work tree, so the work tree must be what
# is staged: a change not staged, or a new file not added, stops it before the checks, and a file the checks change
# stops it after them. Then agents/ decoded, lean/ built and its proofs checked, and the export checked.
STAGED = git diff --quiet && test -z "$$(git ls-files --others --exclude-standard)"

verify: ## the checks for what is staged, run by the pre-commit hook (then the project's own checks)
	@if git diff --cached --name-only | grep -qE '^(PRODUCTS\.md|[^/]+\.lock)$$'; then $(MAKE) products-check; fi
	@$(STAGED) || { echo "verify: the work tree is not what is staged (git status): make verify checks the work tree; stage the rest, or stash it (git stash push --keep-index --include-untracked)"; exit 1; }
	$(MAKE) --no-print-directory agents-check
	$(MAKE) --no-print-directory lean
	$(MAKE) --no-print-directory parts-check
	@$(STAGED) || { echo "verify: make verify changed the work tree (git status): stage what it wrote"; exit 1; }

# ---------------------------------------------------------------- the project's own

agents-check: ## agents/ decoded by the kit, nothing written; make verify runs it
	$(NEEDKIT)
	dev/agents/bin/kit check --root .

# ---------------------------------------------------------------- the Lean (lean/, README.md)

lean: ## the definitions built and every proof checked by Lake, with the shell's Lean once its version is the one lean/lean-toolchain names; a proof left as sorry fails it, and so does a constant of lean/ resting on an axiom other than Lean's three (dev/axioms.lean, every file of lean/); Lake's lines in .reports/lean.log, the audit's in .reports/axioms.log
	@v=$$(lean --version | sed -n 's/^Lean (version \([^,]*\),.*/\1/p'); \
	t=$$(sed 's|^leanprover/lean4:v||' lean/lean-toolchain); \
	[ -n "$$v" ] && [ "$$t" = "$$v" ] || { echo "lean: the shell's Lean is '$$v', lean/lean-toolchain names '$$t'"; exit 1; }
	@mkdir -p .reports
	@cd lean && lake build 2>&1 | tee ../.reports/lean.log; test $${PIPESTATUS[0]} -eq 0
	@! grep -q "declaration uses .sorry." .reports/lean.log || { echo "lean: a proof is left as sorry (.reports/lean.log)"; exit 1; }
	@cd lean && lake env lean ../dev/axioms.lean > ../.reports/axioms.log 2>&1 || { grep -E "AXIOMS|error" ../.reports/axioms.log; echo "lean: the axiom audit failed (.reports/axioms.log)"; exit 1; }
	@tail -n 1 .reports/axioms.log

# ---------------------------------------------------------------- the open parts (export/parts.json, README.md)

# The product's one number: flake.nix's version (README.md, Changes), which make parts writes into the export.
VERSION := $(shell sed -n 's/^ *version = "\([^"]*\)";$$/\1/p' flake.nix)
# The file make parts-check reads: export/parts.json, or another given by PARTS=.
PARTS ?= export/parts.json

# The export made by Lean into $(1) (dev/parts.lean), from lean/ as built: it stops where lean/ is not built as it
# stands (make lean), or flake.nix has not one version.
define parts-into
	@[ -n "$(VERSION)" ] && [ "$$(printf '%s\n' $(VERSION) | wc -l)" -eq 1 ] || { echo "$@: not one version = \"...\"; in flake.nix"; exit 1; }
	@cd lean && lake build --no-build -q || { echo "$@: lean/ is not built as it stands: make lean"; exit 1; }
	@mkdir -p $(dir $(1))
	@cd lean && PARTS_VERSION=$(VERSION) PARTS_OUT=$(abspath $(1)) lake env lean ../dev/parts.lean
endef

parts: ## the definition's open parts, export/parts.json, made by Lean from lean/ as built (dev/parts.lean; README.md, The open parts), its version flake.nix's; after make lean
	$(call parts-into,export/parts.json)

parts-check: ## whether export/parts.json is what Lean gives (made again into .reports/parts.json, compared byte for byte), then its form (dev/parts.check.py); PARTS=<file> checks another file
	$(call parts-into,.reports/parts.json)
	@cmp -s .reports/parts.json $(PARTS) || { echo "parts-check: $(PARTS) is not what Lean gives (.reports/parts.json): make parts"; exit 1; }
	@$(PY) -I dev/parts.check.py $(PARTS) $(VERSION)
