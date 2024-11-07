# SPDX-License-Identifier: Apache-2.0
{ buildEnv
, cbmc
, fetchFromGitHub
, callPackage
, bitwuzla
, ninja
, cadical
}:

buildEnv {
  name = "pqcp-cbmc";
  paths =
    builtins.attrValues {
      cbmc = cbmc.overrideAttrs (old: rec {
        version = "6.3.1"; # remember to adjust this in ../flake.nix too
        src = fetchFromGitHub {
          owner = "diffblue";
          repo = old.pname;
          rev = "${old.pname}-${version}";
          hash = "sha256-y3avPsVxtxSV+WB8TBbvnaNZ4WZltGRTcD+GPwTlp2E=";
        };
        patches = [
          ./0001-Do-not-download-sources-in-cmake.patch
        ];
      });
      litani = callPackage ./litani.nix { }; # 1.29.0
      cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.9

      z3 = callPackage ./z3.nix {
        version = "4.13.3";
        sha256 = "sha256-odwalnF00SI+sJGHdIIv4KapFcfVVKiQ22HFhXYtSvA=";
      };

      inherit
        cadical#1.9.5
        bitwuzla# 0.6.0
        ninja; # 1.11.1
    };
}
