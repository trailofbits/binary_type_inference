let pkgs = import <nixpkgs> {};
    p = { lib, fetchFromGitHub, rustPlatform }:
      rustPlatform.buildRustPackage rec {
        pname = "binary_type_inference";
        version = "0.1.0";

        src = ./.;
        cargoSha256 = "sha256-+3Sb7BhxCJTm7UbJ31sjggyHBJD826d5T1+c6l2gW6g=";
      };
in pkgs.rustPackages.callPackage p {}
