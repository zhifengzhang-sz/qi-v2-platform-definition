# qi-v2-platform-definition's tools and product, the same on every machine (docs/process.md): `nix develop`, then
# `make install` and the targets of the Makefile. Everything from outside is an input pinned by flake.lock: qi-v2's
# one nixpkgs, its pure shell and its Lean; the kit, which writes the agents' files from agents/. The product,
# qi-v2-platform-definition (README.md), is the package of the same name: the Lake package of lean/, as source.
{
  description = "qi-v2-platform-definition: the platform's formal definition in Lean, on Kahn process networks";

  inputs.qi-v2.url = "github:zhifengzhang-sz/qi-v2-nix?dir=qi-v2";
  inputs.nixpkgs.follows = "qi-v2/nixpkgs";
  inputs.kit.url = "github:zhifengzhang-sz/qi-v2-nix?dir=kit";
  inputs.kit.inputs.qi-v2.follows = "qi-v2";

  outputs = { self, nixpkgs, qi-v2, kit }:
    let
      lib = nixpkgs.lib;
      # the systems qi-v2's Lean is pinned for
      systems = [ "x86_64-linux" ];
      forAll = f: lib.genAttrs systems (system: f (import nixpkgs {
        inherit system;
        config.allowUnfreePredicate = pkg: builtins.elem (lib.getName pkg) [ "claude-code" "github-copilot-cli" ];
      }));
      # The product's one number (README.md, Changes).
      version = "0.1.0";
    in {
      # The product: lean/, the Lake package, as source, for a taker's Lake; with README.md and LICENSE.
      packages = forAll (pkgs:
        let
          qi-v2-platform-definition = pkgs.runCommand "qi-v2-platform-definition-${version}" { } ''
            mkdir -p $out
            cp -r ${./lean}/. $out/
            cp ${./README.md} $out/README.md
            cp ${./LICENSE} $out/LICENSE
          '';
        in {
          inherit qi-v2-platform-definition;
          default = qi-v2-platform-definition;
        });

      devShells = forAll (pkgs:
        let
          shell = extra: qi-v2.lib.mkPureShell pkgs {
            name = "qi-v2-platform-definition";
            # the Lean of lean/: qi-v2's lean preset, the version lean/lean-toolchain names (make lean checks it)
            uses = [ (qi-v2.lib.lean pkgs) ];
            packages = with pkgs; [ gnumake git gh curl gzip openssh python3 ] ++ extra;
            hostTools = [ "nix" "nix-store" ];
            env = { QI_DEFINITION_SHELL = "1"; };
            closing = ''echo "qi-v2-platform-definition: make help lists the targets; docs/opening.md says where the work stands"'';
          };
        in {
          default = shell [ ];
          claude-code = shell [ pkgs.claude-code ];
          copilot = shell [ pkgs.github-copilot-cli ];
        });
    };
}
