# SPDX-License-Identifier: Apache-2.0

{ stdenvNoCC
, fetchurl
}:

stdenvNoCC.mkDerivation rec {
  pname = "gcc-arm";
  version = "13.2.rel1";

  platform = "x86_64";

  platform_suffix = "linux-gnu";

  src = fetchurl {
    url = "https://developer.arm.com/-/media/Files/downloads/gnu/${version}/binrel/arm-gnu-toolchain-${version}-${platform}-aarch64-none-${platform_suffix}.tar.xz";
    sha256 = "sha256-EvzfE6dDBlUimyBDiknoVm4mVRugh1mSLNr0aVsNTiM=";
  };

  dontConfigure = true;
  dontBuild = true;
  dontPatchELF = true;
  dontStrip = true;

  installPhase = ''
    mkdir -p $out
    cp -r * $out
  '';

  meta = {
    description = "Pre-built cross-compiled aarch64 gcc for x86_64 linux";
    homepage = "https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads";
    platforms = [ "x86_64-linux" ];
  };
}
