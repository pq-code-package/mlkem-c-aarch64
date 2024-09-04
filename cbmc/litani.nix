# SPDX-License-Identifier: Apache-2.0

{ stdenvNoCC
, fetchFromGitHub
}:

stdenvNoCC.mkDerivation {
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
    mkdir -p $out/bin
    cp litani $out/bin
    cp -r lib $out/bin
    cp -r templates $out/bin
  '';
  dontStrip = true;
  noAuditTmpdir = true;

  meta = {
    description = "Litani metabuild system";
    homepage = "https://awslabs.github.io/aws-build-accumulator/";
  };
}
