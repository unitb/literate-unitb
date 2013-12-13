
Verifier.so: cpipeline.hs lib.c *.hs */*.hs */*/*.hs haskell.h
	ghc -O --make \
		-no-hs-main -optl '-shared'  \
		-optc-O lib.c CPipeline          \
		-threaded                     \
		-o Verifier.so 

xVerifier.so: safe.hs test.c Haskell.h
	ghc -O --make \
		-no-hs-main -optl '-shared'  \
		-optc-O Browser          \
		-o Verifier.so

GUI/EIFGENs/literate_unitb_browser/W_code/literate_unitb_browser: Verifier.so GUI/*.e GUI/*/*.e
	cd GUI
	ec -freeze -config *.ecf
	cd GUI/EIFGENs/literate_unitb_browser/W_code
	finish_freezing

run: GUI/EIFGENs/literate_unitb_browser/W_code/literate_unitb_browser
	GUI/EIFGENs/literate_unitb_browser/W_code/literate_unitb_browser
