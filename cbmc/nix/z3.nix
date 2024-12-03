# SPDX-License-Identifier: MIT

{ version
, sha256
, fetchFromGitHub
, fixDarwinDylibNames
, lib
, stdenv
, python3Packages
, llvmPackages
}:
stdenv.mkDerivation rec {
  inherit version sha256;
  pname = "z3";
  src = fetchFromGitHub {
    inherit sha256;
    owner = "Z3Prover";
    repo = "z3";
    rev = "z3-${version}";
  };

  nativeBuildInputs = [ python3Packages.python ]
    ++ lib.optional stdenv.hostPlatform.isLinux llvmPackages.libcxxClang
    ++ lib.optional stdenv.hostPlatform.isDarwin fixDarwinDylibNames;

  enableParallelBuilding = true;

  configurePhase = ''
    python scripts/mk_make.py --prefix=$out
    cd build
  '';

  checkPhase = ''
    make test
    ./test-z3 -a
  '';

  postInstall = ''
    mkdir -p $dev $lib
    mv $out/lib $lib/lib
    mv $out/include $dev/include
  '';

  outputs = [ "out" "lib" "dev" ];
}
