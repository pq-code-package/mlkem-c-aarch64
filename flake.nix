# SPDX-License-Identifier: Apache-2.0

{
  description = "mlkem-c-aarch64";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, nixpkgs, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { pkgs, system, inputs', ... }:
        let
          core = with pkgs; [
            # formatter & linters
            astyle # 3.4.10
            nixpkgs-fmt
            shfmt
          ];
        in
        {
          devShells.default = with pkgs; mkShellNoCC {
            packages = core ++ [
              direnv
              nix-direnv
            ];

            shellHook = ''
              export PATH=$PWD/scripts:$PWD/scripts/ci:$PATH
            '';
          };

          devShells.ci = with pkgs; mkShellNoCC {
            packages = core;
            shellHook = ''
              export PATH=$PWD/scripts:$PWD/scripts/ci:$PATH
            '';
          };

        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}

