let
  args = { bundle = "8.20"; inNixShell = true; };
  nixpkgs = import ./default.nix args;
  pkgs = nixpkgs.pkgs;
  # push cache:
  # nix-build codespace.nix | cachix push markuskl-ssprove
in pkgs.mkShell {
  packages = with pkgs; [
    coqPackages.coq
    coqPackages.coq-lsp
    coqPackages.ssprove
    gnumake
  ];
}
