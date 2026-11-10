# qi-v2-platform-definition: what it owns, gives and takes

## Responsibility

It owns the platform's formal definition in Lean: the base (Kahn process networks: logs, processes, networks), Kafka's topic, the four components (acquisition, warehousing, visualization, the market model engine) and their wiring, every claim about them proved. It gives the definition as one product, `qi-v2-platform-definition`. It does not own any component's code, which is each component's own project's; the tools, Lean and the kit are taken, not owned.

## Products

| Product | What | Form | Version | Release | Doc |
|---|---|---|---|---|---|
| `qi-v2-platform-definition` | the Lake package of `lean/`, as source: the base, Kafka's topic, the four components and their wiring | flake package | 0.1.0 | `qi-v2-platform-definition-0.1.0` | `README.md` |

## Takes

| Product | From | Pinned by |
|---|---|---|
| `qi-v2` | `qi-v2-nix` | `flake.lock` |
| `nixpkgs` | `qi-v2`, which it follows | `flake.lock` |
| `kit` | `qi-v2-nix` | `flake.lock` |
