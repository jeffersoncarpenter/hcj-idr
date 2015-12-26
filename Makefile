export PATH := .cabal-sandbox/bin:PATH

all:
	idris --codegen javascript -isrc src/Main.idr -o dist/Main.js
