let
  pkgs = import <nixpkgs> {};
  src = pkgs.fetchFromGitHub {
    owner = "SSProve";
    repo = "ssprove";
    rev = "b57e83e18e77c65c4bd32b462b2d2f0a924c726a";
    sha256 = "cQVopnL0thyYJ0QJhD5DCUSjK34RBsWbnJazh0eL5qw=";
  };
in import "${src}/default.nix"
