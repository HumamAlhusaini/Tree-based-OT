{
  description = "Haskell development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }: 
    flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = import nixpkgs { inherit system; };

        haskellPackages = pkgs.haskell.packages.ghc96; # Choose GHC version
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = with haskellPackages; [
            ghc
            cabal-install
            haskell-language-server
          ];

          shellHook = ''
            echo "Welcome to your Haskell development environment!"
            echo "GHC Version: $(ghc --version)"
          '';
        };
      }
    );
}

