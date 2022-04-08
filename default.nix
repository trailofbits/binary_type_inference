let
  pkgs = import <nixpkgs> { };


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
  paths = [ rust-bin ];
}
