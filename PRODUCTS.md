# qi-v2-platform-definition: what it owns, gives and takes

## Responsibility

It owns the platform's formal definition in Lean: the base (Kahn process networks: logs, processes, networks), the contract specs (the formal definition of market's and chanlun's contracts, their records and their rules), Kafka's topic, the four components (acquisition, warehousing, visualization, the market model engine), each taking the contracts' records, and their wiring, every claim about them proved. It gives the definition as one product, `qi-v2-platform-definition`, with the export of its open parts. It does not own any component's code, which is each component's own project's; the tools, Lean and the kit are taken, not owned.

## Products

| Product | What | Form | Version | Release | Doc |
|---|---|---|---|---|---|
| `qi-v2-platform-definition` | the Lake package of `lean/`, as source: the base, the contract specs, Kafka's topic, the four components and their wiring; with `export/parts.json`, the definition's open parts | flake package | 0.2.0 | `qi-v2-platform-definition-0.2.0` | `README.md` |

## Takes

| Product | From | Pinned by |
|---|---|---|
| `qi-v2` | `qi-v2-nix` | `flake.lock` |
| `nixpkgs` | `qi-v2`, which it follows | `flake.lock` |
| `kit` | `qi-v2-nix` | `flake.lock` |
