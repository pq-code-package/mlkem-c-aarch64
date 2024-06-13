# SPDX-License-Identifier: Apache-2.0

{
  description = "mlkem-c-aarch64";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";

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
          litani = pkgs.callPackage ./litani.nix { };
          cbmc-viewer = pkgs.callPackage ./cbmc-viewer.nix { };
          astyle = pkgs.astyle.overrideAttrs (old: rec {
            version = "3.4.13";
            src = pkgs.fetchurl {
              url = "mirror://sourceforge/${old.pname}/${old.pname}-${version}.tar.bz2";
              hash = "sha256-eKYQq9OelOD5E+nuXNoehbtizWM1U97LngDT2SAQGc4=";
            };
          });
          cbmc = pkgs.cbmc.overrideAttrs (old: rec {
            version = "731338d5d82ac86fc447015e0bd24cdf7a74c442";
            src = pkgs.fetchFromGitHub {
              owner = "diffblue";
              repo = old.pname;
              rev = "${version}";
              hash = "sha256-fDLSo5EeHyPTliAqFp+5mfaB0iZXIMXeMyF21fjl5k4=";
            };
          });

          core = builtins.attrValues
            {
              litani = litani; # 1.29.0
              cbmc-viewer = cbmc-viewer; # 3.8
              astyle = astyle;
              cbmc = cbmc;

              inherit (pkgs)
                ninja# 1.11.1
                qemu# 8.2.4
                # formatter & linters
                cadical
                nixpkgs-fmt
                shfmt;

              inherit (pkgs.python3Packages)
                python
                black
                click;
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
