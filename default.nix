let
  pkgs = import <nixpkgs> { };

  lowering-datalog = pkgs.stdenv.mkDerivation
    {
      name = "lowering-datalog";
      src = ./.;

      nativeBuildInputs = [ pkgs.souffle ];

      buildPhase = "souffle -o lowertypes ./lowering/type_inference.dl";

      installPhase = ''
        mkdir -p $out/bin
        cp lowertypes $out/bin/
      '';
    };

  p = { lib, fetchFromGitHub, rustPlatform }:
    rustPlatform.buildRustPackage rec {
      pname = "binary_type_inference";
      version = "0.1.0";

      src = ./.;
      cargoLock = {
        lockFile = ./Cargo.lock;
      };
    };

  rust-bin = pkgs.rustPackages.callPackage p { };
in
pkgs.symlinkJoin {
  name = "bti";
  paths = [ rust-bin lowering-datalog ];
}
