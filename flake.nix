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

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { pkgs, system, ... }:
        let
          core = builtins.attrValues
            {
              inherit (pkgs)
                # formatter & linters
                astyle# 3.4.10
                cadical
                nixpkgs-fmt
                shfmt;
            }
          ++ {
            "x86_64-linux" = [ (pkgs.callPackage ./arm-gnu-gcc.nix { }) ];
            "aarch64-linux" = [ (pkgs.gcc13.override { propagateDoc = true; isGNU = true; }) ];
            "aarch64-darwin" = [ ];
            "x86_64-darwin" = [ ];
          }.${system};

        in
        {
          devShells.default = pkgs.mkShellNoCC {
            packages = core ++ builtins.attrValues {
              inherit (pkgs)
                direnv
                nix-direnv;
            };

            shellHook = ''
              export PATH=$PWD/scripts:$PWD/scripts/ci:$PATH
            '';
          };

          devShells.ci = pkgs.mkShellNoCC {
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
