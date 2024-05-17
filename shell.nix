{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
	nativeBuildInputs = with pkgs.buildPackages; [ lld clang ];
	shellHook = ''
		export CC=clang
	'';
}
