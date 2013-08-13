First, at the root of literate-unitb, create a directory called bin and put the binary executable of z3. 
Second, open a terminal at the root of literate-unitb and type

	ghc run_tests.hs
	./run_tests

A series of test results should appear ending with

	***********
	* SUCCESS *
	***********

As a rule, do not publish a commit unless (0) the tests have been run just before the commit and (1) the tests are successful.

