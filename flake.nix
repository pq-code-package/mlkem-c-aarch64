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

          native-gcc =
            if pkgs.stdenv.isDarwin
            then null
            else wrap-gcc pkgs;

          # cross is for determining whether to install the cross toolchain or not
          core = { cross ? true }:
            let
              x86_64-gcc = wrap-gcc pkgs.pkgsCross.gnu64;
              aarch64-gcc = wrap-gcc pkgs.pkgsCross.aarch64-multiplatform;
              riscv64-gcc = wrap-gcc pkgs.pkgsCross.riscv64;
              mips64-gcc = wrap-gcc pkgs.pkgsCross.mips64-linux-gnuabi64;
            in
            # NOTE:
              # - native toolchain should be equipped in the shell via `mkShellWithCC` (see `mkShell`)
              # - only install extra cross-compiled toolchains if not on darwin or `cross` is specifally set to true
              # - providing cross compilation toolchain (x86_64/aarch64-linux) for darwin can be cumbersome
              #   and won't just work for now
              # - equip all toolchains if cross is explicitly set to true
              # - On some machines, `native-gcc` needed to be evaluated lastly (placed as the last element of the toolchain list), or else would result in environment variables (CC, AR, ...) overriding issue.
            pkgs.lib.optionals (cross && !pkgs.stdenv.isDarwin) [
              (pkgs.lib.optional (! pkgs.stdenv.hostPlatform.isx86_64) x86_64-gcc)
              (pkgs.lib.optional (! pkgs.stdenv.hostPlatform.isAarch64) aarch64-gcc)
              (pkgs.lib.optional (! pkgs.stdenv.hostPlatform.isRiscV64) riscv64-gcc)
              (pkgs.lib.optional (! pkgs.stdenv.hostPlatform.isMips64)  mips64-gcc)
              native-gcc
            ]
            ++ builtins.attrValues {
              inherit (config.packages) base;
              inherit (pkgs)
                qemu; # 8.2.4
            };

          wrapShell = mkShell: attrs:
            mkShell (attrs // {
              shellHook = ''
                export PATH=$PWD/scripts:$PWD/scripts/ci:$PATH
              '' +
              # NOTE: we don't support nix gcc toolchains for darwin system, therefore explicitly setting environment variables like CC, AR, AS, ... is required
              pkgs.lib.optionalString pkgs.stdenv.isDarwin ''
                export CC=gcc
                export CXX=g++
                for cmd in \
                    ar as ld nm objcopy objdump readelf ranlib strip strings size windres
                do
                    export ''${cmd^^}=$cmd
                done
              '';
            });

          # NOTE: idiomatic nix way of properly setting the $CC in a nix shell
          mkShellWithCC = cc: pkgs.mkShellNoCC.override { stdenv = pkgs.overrideCC pkgs.stdenv cc; };
          mkShell = mkShellWithCC native-gcc;
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

          packages.cbmc = pkgs.callPackage ./cbmc/nix { }; # 6.4.0

          packages.base = pkgs.buildEnv {
            name = "pqcp-base";
            paths = builtins.attrValues {
              inherit (pkgs.python3Packages)
                pyyaml
                python
                click;
            };
          };

          devShells.default = wrapShell mkShell {
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

          devShells.ci = wrapShell mkShell { packages = core { cross = false; }; };
          devShells.ci-cross = wrapShell mkShell { packages = core { }; };
          devShells.ci-cbmc = wrapShell mkShell { packages = core { cross = false; } ++ [ config.packages.cbmc ]; };
          devShells.ci-cbmc-cross = wrapShell mkShell { packages = core { } ++ [ config.packages.cbmc ]; };
          devShells.ci-linter = wrapShell pkgs.mkShellNoCC { packages = [ config.packages.linters ]; };

          devShells.ci_clang18 = wrapShell (mkShellWithCC pkgs.clang_18) { packages = [ config.packages.base ]; };
          devShells.ci_gcc48 = wrapShell (mkShellWithCC pkgs.gcc48) { packages = [ config.packages.base ]; };
          devShells.ci_gcc49 = wrapShell (mkShellWithCC pkgs.gcc49) { packages = [ config.packages.base ]; };
          devShells.ci_gcc7 = wrapShell (mkShellWithCC pkgs.gcc7) { packages = [ config.packages.base ]; };
          devShells.ci_gcc11 = wrapShell (mkShellWithCC pkgs.gcc11) { packages = [ config.packages.base ]; };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
