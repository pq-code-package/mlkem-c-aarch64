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
            inherit (pkgs)
              nixpkgs-fmt
              clang-tools
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

          cross =
            let
              gcc_all =
                if pkgs.stdenv.isDarwin
                then [ ]
                else [ aarch64-gcc x86_64-gcc ];
            in
            gcc_all;

          core =
            let
              gcc =
                if pkgs.stdenv.isDarwin
                then [ ]
                else if pkgs.stdenv.isAarch64
                then [ aarch64-gcc ]
                else
                  [ x86_64-gcc ];
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
            packages = core ++ linters ++ cbmcpkg ++
              builtins.attrValues {
                inherit (pkgs)
                  direnv
                  nix-direnv;
              };
          };

          devShells.bench = wrapShell pkgs.mkShellNoCC { packages = core; };
          devShells.ci = wrapShell pkgs.mkShellNoCC { packages = core ++ cross; };
          devShells.ci-cbmc = wrapShell pkgs.mkShellNoCC { packages = core ++ cbmcpkg; };
          devShells.ci-linter = wrapShell pkgs.mkShellNoCC { packages = linters; };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
