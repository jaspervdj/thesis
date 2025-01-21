{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  packages = [
    pkgs.inconsolata
    pkgs.texlive.combined.scheme-full
    pkgs.haskellPackages.lhs2tex
    (pkgs.rWrapper.override {
        packages = [ pkgs.rPackages.plotrix ];
    })
  ];
}
