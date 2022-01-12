{
  description = "Binary type inference";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    naersk.url = "github:nix-community/naersk";
  };

  outputs = { self, nixpkgs, flake-utils, naersk }:
      flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = nixpkgs.legacyPackages.${system};
        naersk-lib = naersk.lib."${system}";
        binary_type_inference = naersk-lib.buildPackage {
        pname = "my-project";
        root = ./.;
      };
      in {
        defaultPackage = binary_type_inference;
        devShell = pkgs.mkShell { buildInputs = [ pkgs.cargo pkgs.rustc pkgs.souffle ]; };
      });
}
