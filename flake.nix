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
      perSystem = { pkgs, ... }:
        let
          cbmcpkg = pkgs.callPackage ./cbmc { }; # 6.3.1

          linters = builtins.attrValues {
            astyle = pkgs.astyle.overrideAttrs (old: rec {
              version = "3.4.13";
              src = pkgs.fetchurl {
                url = "mirror://sourceforge/${old.pname}/${old.pname}-${version}.tar.bz2";
                hash = "sha256-eKYQq9OelOD5E+nuXNoehbtizWM1U97LngDT2SAQGc4=";
              };
            });

            inherit (pkgs)
              nixpkgs-fmt
              clang-tools
              shfmt;

            inherit (pkgs.python3Packages)
              black;
          };

          aarch64-gcc = [
            (
              pkgs.pkgsCross.aarch64-multiplatform.buildPackages.gcc13.override {
                propagateDoc = true;
                isGNU = true;
              }
            )
            pkgs.pkgsCross.aarch64-multiplatform.glibc
            pkgs.pkgsCross.aarch64-multiplatform.glibc.static
          ];

          native-gcc = [
            (pkgs.gcc13.override {
              propagateDoc = true;
              isGNU = true;
            })
            pkgs.glibc
            pkgs.glibc.static
          ];

          core = { cross ? false }:
            let
              gcc =
                if pkgs.stdenv.isDarwin
                then
                  if pkgs.stdenv.isx86_64
                  then [ ]
                  else aarch64-gcc
                else
                  if cross
                  then aarch64-gcc
                  else native-gcc
              ;
            in
            gcc ++
            builtins.attrValues {
              inherit (pkgs)
                yq
                ninja# 1.11.1
                qemu# 8.2.4
                cadical;

              inherit (pkgs.python3Packages)
                python
                click;
            };

          wrapShell = mkShell: attrs:
            mkShell (attrs // {
              shellHook = ''
                export PATH=$PWD/scripts:$PWD/scripts/ci:$PATH
              '';
            });
        in
        {
          devShells.default = wrapShell pkgs.mkShellNoCC {
            packages = core { } ++ linters ++ cbmcpkg ++
              builtins.attrValues {
                inherit (pkgs)
                  direnv
                  nix-direnv;
              };
          };

          devShells.x86_64-linux-cross = wrapShell pkgs.mkShellNoCC {
            packages = core { cross = true; } ++ linters ++ cbmcpkg ++
              builtins.attrValues {
                inherit (pkgs)
                  direnv
                  nix-direnv;
              };
          };

          devShells.ci = wrapShell pkgs.mkShellNoCC { packages = core { }; };
          devShells.x86_64-linux-cross-ci = wrapShell pkgs.mkShellNoCC {
            packages = core { cross = true; };
          };

          devShells.ci-cbmc = wrapShell pkgs.mkShellNoCC { packages = core { } ++ cbmcpkg; };
          devShells.x86_64-linux-cross-ci-cbmc = wrapShell pkgs.mkShellNoCC {
            packages = core { cross = true; } ++ cbmcpkg;
          };

          devShells.ci-linter = wrapShell pkgs.mkShellNoCC { packages = linters; };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
