# SPDX-License-Identifier: Apache-2.0

{
  description = "mlkem-native";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    nixpkgs-unstable.url = "github:NixOS/nixpkgs/nixos-unstable";

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, pkgs, system, inputs', ... }:
        let
          default_gcc = { cross ? true }:
            let
              glibc-join = p: p.buildPackages.symlinkJoin {
                name = "glibc-join";
                paths = [ p.glibc p.glibc.static ];
              };

              wrap-gcc = p: p.buildPackages.wrapCCWith {
                cc = p.buildPackages.gcc13.cc;
                bintools = p.buildPackages.wrapBintoolsWith {
                  bintools = p.buildPackages.binutils-unwrapped;
                  libc = glibc-join p;
                };
              };

              x86_64-gcc = wrap-gcc pkgs.pkgsCross.gnu64;
              aarch64-gcc = wrap-gcc pkgs.pkgsCross.aarch64-multiplatform;
            in
            if pkgs.stdenv.isDarwin
            then [ ]
            else if cross
            then if pkgs.stdenv.isAarch64
            then [ x86_64-gcc aarch64-gcc ]
            else [ aarch64-gcc x86_64-gcc ]
            else if pkgs.stdenv.isAarch64
            then [ aarch64-gcc ]
            else [ x86_64-gcc ];

          # cross is for determining whether to install the cross toolchain or not 
          core = { cross ? true }:
            [ (default_gcc { cross = cross; }) ] ++
            builtins.attrValues {
              inherit (config.packages) base;
              inherit (pkgs)
                qemu; # 8.2.4
            };

          wrapShell = mkShell: attrs:
            mkShell (attrs // {
              shellHook = ''
                export PATH=$PWD/scripts:$PWD/scripts/ci:$PATH
              '';
            });
        in
        {
          # NOTE: hack for replacing bitwuzla in nixos-24.05 (0.4.0) to the one in nixos-unstable (0.6.0) by nix overlays
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              (_: _: { bitwuzla = inputs'.nixpkgs-unstable.legacyPackages.bitwuzla; })
            ];
          };

          packages.linters = pkgs.buildEnv
            {
              name = "pqcp-linters";
              paths = builtins.attrValues {
                clang-tools = pkgs.clang-tools.overrideAttrs {
                  unwrapped = pkgs.llvmPackages_17.clang-unwrapped;
                };

                inherit (pkgs)
                  nixpkgs-fmt
                  shfmt;

                inherit (pkgs.python3Packages)
                  black;
              };
            };

          packages.cbmc = pkgs.callPackage ./cbmc { }; # 6.3.1

          packages.base = pkgs.buildEnv {
            name = "pqcp-base";
            paths = builtins.attrValues {
              inherit (pkgs.python3Packages)
                pyyaml
                python
                click;
            };
          };


          devShells.default = wrapShell pkgs.mkShellNoCC {
            packages =
              core { } ++
              builtins.attrValues
                {
                  inherit (config.packages) linters cbmc;
                  inherit (pkgs)
                    direnv
                    nix-direnv;
                };
          };

          devShells.ci = wrapShell pkgs.mkShellNoCC { packages = core { cross = false; }; };
          devShells.ci-cross = wrapShell pkgs.mkShellNoCC { packages = core { }; };
          devShells.ci-cbmc = wrapShell pkgs.mkShellNoCC { packages = core { cross = false; } ++ [ config.packages.cbmc ]; };
          devShells.ci-cbmc-cross = wrapShell pkgs.mkShellNoCC { packages = core { } ++ [ config.packages.cbmc ]; };
          devShells.ci-linter = wrapShell pkgs.mkShellNoCC { packages = [ config.packages.linters ]; };

          devShells.ci_clang18 = wrapShell pkgs.mkShellNoCC { packages = [ config.packages.base pkgs.clang_18 ]; };
          devShells.ci_gcc48 = wrapShell pkgs.mkShellNoCC { packages = [ config.packages.base pkgs.gcc48 ]; };
          devShells.ci_gcc49 = wrapShell pkgs.mkShellNoCC { packages = [ config.packages.base pkgs.gcc49 ]; };
          devShells.ci_gcc7 = wrapShell pkgs.mkShellNoCC { packages = [ config.packages.base pkgs.gcc7 ]; };
          devShells.ci_gcc11 = wrapShell pkgs.mkShellNoCC { packages = [ config.packages.base pkgs.gcc11 ]; };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
