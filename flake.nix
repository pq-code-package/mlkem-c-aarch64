# SPDX-License-Identifier: Apache-2.0

{
  description = "mlkem-native";

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
            clang-tools = pkgs.clang-tools.overrideAttrs {
              unwrapped = pkgs.llvmPackages_17.clang-unwrapped;
            };

            inherit (pkgs)
              nixpkgs-fmt
              shfmt;

            inherit (pkgs.python3Packages)
              black;
          };

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

          default_gcc = { cross ? true }:
            let
              gcc =
                if pkgs.stdenv.isDarwin
                then [ ]
                else
                  if cross
                  then
                    if pkgs.stdenv.isAarch64
                    then [ x86_64-gcc aarch64-gcc ]
                    else [ aarch64-gcc x86_64-gcc ]
                  else
                    if pkgs.stdenv.isAarch64
                    then [ aarch64-gcc ]
                    else [ x86_64-gcc ];
            in
            gcc;

          base =
            builtins.attrValues {
              inherit (pkgs.python3Packages)
                pyyaml
                python
                click;
            };

          # cross is for determining whether to install the cross toolchain or not
          core = { cross ? true }:
            default_gcc { cross = cross; } ++ base ++
            builtins.attrValues {
              inherit (pkgs)
                qemu; # 8.2.4
            };

          core_gcc48 = base ++ builtins.attrValues {
            inherit (pkgs)
              gcc48; #4.8
          };

          core_gcc49 = base ++ builtins.attrValues {
            inherit (pkgs)
              gcc49; #4.9
          };

          core_gcc7 = base ++ builtins.attrValues {
            inherit (pkgs)
              gcc7; #7
          };

          core_gcc11 = base ++ builtins.attrValues {
            inherit (pkgs)
              gcc11; #11
          };

          core_clang18 = base ++ builtins.attrValues {
            inherit (pkgs)
              clang_18; #18
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

          devShells.ci = wrapShell pkgs.mkShellNoCC { packages = core { cross = false; }; };
          devShells.ci-cross = wrapShell pkgs.mkShellNoCC { packages = core { }; };
          devShells.ci-cbmc = wrapShell pkgs.mkShellNoCC { packages = core { cross = false; } ++ cbmcpkg; };
          devShells.ci-cbmc-cross = wrapShell pkgs.mkShellNoCC { packages = core { } ++ cbmcpkg; };
          devShells.ci-linter = wrapShell pkgs.mkShellNoCC { packages = linters; };

          devShells.ci_clang18 = wrapShell pkgs.mkShellNoCC { packages = core_clang18; };
          devShells.ci_gcc48 = wrapShell pkgs.mkShellNoCC { packages = core_gcc48; };
          devShells.ci_gcc49 = wrapShell pkgs.mkShellNoCC { packages = core_gcc49; };
          devShells.ci_gcc7 = wrapShell pkgs.mkShellNoCC { packages = core_gcc7; };
          devShells.ci_gcc11 = wrapShell pkgs.mkShellNoCC { packages = core_gcc11; };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
