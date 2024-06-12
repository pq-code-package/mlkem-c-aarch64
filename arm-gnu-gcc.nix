# SPDX-License-Identifier: Apache-2.0

{ stdenvNoCC
, fetchurl
}:

stdenvNoCC.mkDerivation rec {
  pname = "gcc-arm";
  version = "13.2.rel1";

  platform = {
    x86_64-linux = "x86_64";
  }.${stdenvNoCC.hostPlatform.system} or (throw "Unsupported system: ${stdenvNoCC.hostPlatform.system}");

  platform_suffix = {
    x86_64-linux = "linux-gnu";
  }.${stdenvNoCC.hostPlatform.system} or (throw "Unsupported system: ${stdenvNoCC.hostPlatform.system}");

  src = fetchurl {
    url = "https://developer.arm.com/-/media/Files/downloads/gnu/${version}/binrel/arm-gnu-toolchain-${version}-${platform}-aarch64-none-${platform_suffix}.tar.xz";
    sha256 = {
      x86_64-linux = "sha256-EvzfE6dDBlUimyBDiknoVm4mVRugh1mSLNr0aVsNTiM=";
    }.${stdenvNoCC.hostPlatform.system} or (throw "Unsupported system: ${stdenvNoCC.hostPlatform.system}");
  };

  dontConfigure = true;
  dontBuild = true;
  dontPatchELF = true;
  dontStrip = true;

  installPhase = ''
    mkdir -p $out
    cp -r * $out
  '';
}
