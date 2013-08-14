Compiling and Running the Tests
===============================

First, at the root of literate-unitb, create a directory called bin and put the binary executable of z3. 
Second, open a terminal at the root of literate-unitb and type

	ghc run_tests.hs
	./run_tests

A series of test results should appear ending with

	***********
	* SUCCESS *
	***********

Git
===

As a rule, do not publish a commit unless (0) the tests have been run just before the commit and (1) the tests are successful.

In order to stay up to date with the project's lead developments (today known under the pseudonym cipher1024), enter the command:

    git remote cipher https://github.com/cipher1024/literate-unitb.git

then, any time you need to update one of the branches (most likely the master branch):

    git pull cipher master
