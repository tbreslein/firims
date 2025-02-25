{
  description = "rust library for a fixed range bit set";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/24.05";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs =
    inputs @ { self
    , rust-overlay
    , flake-parts
    , ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      perSystem =
        { system
        , pkgs
        , self'
        , ...
        }:
        let
          buildInputs = [
            pkgs.openssl
            pkgs.pkg-config
            (pkgs.rust-bin.stable."1.80.0".default.override {
              extensions = [ "rust-src" "rust-analyzer" "rustfmt" ];
            })
          ];
        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [ (import rust-overlay) ];
          };
          devShells.default = pkgs.mkShell {
            inherit buildInputs;
          };
        };
    };
}
