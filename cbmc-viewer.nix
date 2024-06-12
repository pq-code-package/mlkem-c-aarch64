# SPDX-License-Identifier: Apache-2.0
{ python3Packages
, fetchurl
}:

python3Packages.buildPythonApplication rec {
  pname = "cbmc-viewer";
  version = "3.8";
  src = fetchurl {
    url = "https://github.com/model-checking/${pname}/releases/download/viewer-${version}/cbmc_viewer-${version}-py3-none-any.whl";
    hash = "sha256-a73odd7mt8uB7qq7yPt/IZNZe/WFvRQDOX8JuHobihQ=";
  };
  format = "wheel";
  dontUseSetuptoolsCheck = true;

  propagatedBuildInputs = [
    python3Packages.voluptuous
    python3Packages.setuptools
    python3Packages.jinja2
  ];

  meta = {
    description = "CBMC Viewer is a tool that scans the output of CBMC";
    homepage = "https://model-checking.github.io/cbmc-viewer/";
  };
}
