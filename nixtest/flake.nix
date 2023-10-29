{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };
  outputs = { self, nixpkgs }:
    let
      system = "aarch64-darwin";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      packages.${system}.default = pkgs.hello;
      apps.${system}.default = {
        type = "app";
        program = "${pkgs.hello}/bin/hello";
      };
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          pkgs.hello
        ];
      };
    };
}