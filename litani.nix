# SPDX-License-Identifier: Apache-2.0

{ lib
, stdenvNoCC
, fetchFromGitHub
, targets ? [ ]
}:

stdenvNoCC.mkDerivation rec {
  pname = "litani";
  version = "8002c240ef4f424039ed3cc32e076c0234d01768";
  src = fetchFromGitHub {
    owner = "awslabs";
    repo = "aws-build-accumulator";
    rev = "8002c240ef4f424039ed3cc32e076c0234d01768";
    sha256 = "sha256-UwF/B6lpsjpQn8SW+tCfOXTp14pNBr2sRGujJH3iPLk=";
  };
  dontConfigure = true;
  installPhase = ''
    mkdir -p $out/litani/
    cp  litani $out/litani/
    cp -r lib $out/litani/
    cp -r templates $out/litani/

    mkdir -p $out/bin
    ln -sf $out/litani/litani $out/bin/litani
  '';
  dontStrip = true;
  noAuditTmpdir = true;

  meta = {
    description = "Litani metabuild system";
    homepage = "https://awslabs.github.io/aws-build-accumulator/";
  };
}
