# qi-v2-platform-definition (README.md): make targets, run inside `nix develop` (flake.nix, docs/process.md), which
# gives every tool they call (flake.nix's shell), and the kit at dev/agents (make install); of the host, only nix.
# Outside it, make stops.
ifneq ($(QI_DEFINITION_SHELL),1)
$(error run make inside this project's shell: nix develop, then make …, or nix develop -c make … (docs/process.md))
endif
SHELL := $(shell command -v bash)
ifeq ($(SHELL),)
$(error no bash in this project's shell)
endif

PY := python3
AGENT_KIND ?= all

.PHONY: help install agents agents-check run-start run-check verify locks-check products-check lean

help: ## the targets
	@grep -E '^[a-z-]+:.*##' $(MAKEFILE_LIST) | sed 's/:.*## /\t/' | expand -t 22

# ---------------------------------------------------------------- the project set up (docs/process.md, The machine)

install: ## the project set up on this machine: git's hooks at dev/hooks (the pre-commit runs make verify); the kit linked at dev/agents from flake.lock's pin, then make agents
	git config core.hooksPath dev/hooks
	@test -n "$(KIT)" || { echo "install: no kit's pin read from flake.lock (nodes.kit.locked)"; exit 1; }
	nix build "$(KIT)" -o dev/agents
	$(MAKE) agents

# The kit at the commit flake.lock pins (nix build --inputs-from drops its ?dir=, so its reference is read from the lock).
KIT := $(shell $(PY) -c "import json; n = json.load(open('flake.lock'))['nodes']['kit']['locked']; print(f\"{n['type']}:{n['owner']}/{n['repo']}/{n['rev']}?dir={n['dir']}\")" 2>/dev/null)

agents: ## each kind's agent files from agents/ (AGENTS.md, CLAUDE.md, .claude/agents/, .github/agents/), by the kit at dev/agents; AGENT_KIND=claude-code|copilot|all; after any change to agents/
	@test -x dev/agents/bin/kit || { echo "agents: no kit at dev/agents: make install"; exit 1; }
	dev/agents/bin/kit generate --kind $(AGENT_KIND) --root .

agents-check: ## agents/ decoded by the kit, nothing written
	@test -x dev/agents/bin/kit || { echo "agents-check: no kit at dev/agents: make install"; exit 1; }
	dev/agents/bin/kit check --root .

run-start: ## before a role's run: the work tree recorded; make run-start ROLE=reviewer
	@test -x dev/agents/bin/kit || { echo "run-start: no kit at dev/agents: make install"; exit 1; }
	@test -n "$(ROLE)" || { echo "run-start: ROLE=<role> is needed"; exit 1; }
	dev/agents/bin/kit run-start --role $(ROLE) --root .

run-check: ## after it: what changed against the role's writes (none: nothing; brief-files: only FILES=a,b; else reported)
	@test -x dev/agents/bin/kit || { echo "run-check: no kit at dev/agents: make install"; exit 1; }
	@test -n "$(ROLE)" || { echo "run-check: ROLE=<role> is needed"; exit 1; }
	dev/agents/bin/kit run-check --role $(ROLE) $(if $(FILES),--files $(FILES)) --root .

verify: ## the checks a commit requires, every one; the pre-commit hook runs it
	$(MAKE) --no-print-directory products-check
	$(MAKE) --no-print-directory agents-check
	$(MAKE) --no-print-directory lean

# kit locks asks each input's source over HTTPS; for a folder input whose repository moved it asks GitHub's compare
# through gh, and where HTTPS fails it asks again by SSH. Both would act with a credential of the owner's, so it runs
# with neither: dev/no-credential's gh, which never runs, first on PATH, and git with no SSH. Where it needs one, it
# stops, naming it, and the owner is asked (agents/rules.md, The credentials).
locks-check: ## whether each lock is outdated: flake.lock's inputs (the kit's kit locks, with no credential); changes nothing
	@test -x dev/agents/bin/kit || { echo "locks-check: no kit at dev/agents: make install"; exit 1; }
	PATH="$(CURDIR)/dev/no-credential:$$PATH" GIT_SSH_COMMAND=false dev/agents/bin/kit locks --root .

products-check: ## whether PRODUCTS.md states what the project has (the kit's kit products)
	@test -x dev/agents/bin/kit || { echo "products-check: no kit at dev/agents: make install"; exit 1; }
	dev/agents/bin/kit products --root .

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
