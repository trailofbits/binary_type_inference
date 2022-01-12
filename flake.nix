{
  description = "Binary type inference";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
      flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = nixpkgs.legacyPackages.${system};
        binary_type_inference = pkgs.rustPlatform.buildRustPackage rec {
            pname = "binary_type_inference";
            version = "0.1.0";
            src = self;
            cargoSha256 = "sha256-cez8pJ/uwj+PHAPQwpSB4CKaxcP8Uvv8xguOrVXR2xE=";
          };
      in {
        defaultPackage = binary_type_inference;
        devShell = pkgs.mkShell { buildInputs = [ pkgs.cargo pkgs.rustc pkgs.souffle ]; };
      });
}
