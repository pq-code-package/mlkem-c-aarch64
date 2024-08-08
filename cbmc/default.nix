# SPDX-License-Identifier: Apache-2.0
{ cbmc
, fetchFromGitHub
, callPackage
, z3_4_12
}:
builtins.attrValues {
  cbmc = cbmc.overrideAttrs (old: rec {
    version = "6.1.1";
    src = fetchFromGitHub {
      owner = "diffblue";
      repo = old.pname;
      rev = "${old.pname}-${version}";
      hash = "sha256-zxlEel/HlCrz4Shy+4WZX7up4qm5h2FoP77kngi8XAo=";
    };
    patches = [
      ./0001-Do-not-download-sources-in-cmake.patch
    ];
  });
  litani = callPackage ./litani.nix { }; # 1.29.0
  cbmc-viewer = callPackage ./cbmc-viewer.nix { }; # 3.9

  inherit
    z3_4_12; # 4.12.5
}
