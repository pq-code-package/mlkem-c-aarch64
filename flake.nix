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
          cbmcpkg = builtins.attrValues
            {
              cbmc = pkgs.cbmc.overrideAttrs (old: rec {
                version = "a8b8f0fd2ad2166d71ccce97dd6925198a018144";
                src = pkgs.fetchFromGitHub {
                  owner = "diffblue";
                  repo = old.pname;
                  rev = "${version}";
                  hash = "sha256-mPRkkKN7Hz9Qi6a3fEwVFh7a9OaBFcksNw9qwNOarao=";
                };
              }); # 6.0.0
              litani = pkgs.callPackage ./litani.nix { }; # 1.29.0
              cbmc-viewer = pkgs.callPackage ./cbmc-viewer.nix { }; # 3.8
            };

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
              shfmt;

            inherit (pkgs.python3Packages)
              black;
          };

          core =
            let
              # for x86_64 machine, cross compiled gcc needed to be wrapped with glibc this way for static compilation
              cross-gcc = with pkgs; wrapCCWith {
                cc = callPackage ./arm-gnu-gcc.nix { };
                bintools = with pkgsCross.aarch64-multiplatform; wrapBintoolsWith {
                  bintools = binutils-unwrapped;
                  libc = glibc.static;
                };
              };
              aarch64-gcc =
                if pkgs.stdenv.isx86_64
                then [ cross-gcc ]
                else [ (pkgs.gcc13.override { propagateDoc = true; isGNU = true; }) pkgs.glibc pkgs.glibc.static ];
            in
            pkgs.lib.optionals pkgs.stdenv.isLinux aarch64-gcc ++
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

          devShells.ci = wrapShell pkgs.mkShellNoCC { packages = core; };
          devShells.ci-cbmc = wrapShell pkgs.mkShellNoCC { packages = (core ++ cbmcpkg); };
          devShells.ci-linter = wrapShell pkgs.mkShellNoCC { packages = linters; };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
