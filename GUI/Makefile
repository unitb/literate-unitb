
HaskellExts.so: safe.hs test.c Haskell.h
	ghc -O --make \
		-no-hs-main -optl '-shared'  \
		-optc-O test.c Safe          \
		-o HaskellExts.so
