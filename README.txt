What you need to do
===================

* Get Haskell Platform
* Get Z3
* Get the Literate Unit-B source
* Run the test suite

Getting a Haskell Platform
==========================

Download the Haskell platform at https://www.haskell.org/

Compiling and Running the Tests
===============================

First, at the root of literate-unitb, create a directory called bin
and put the binary executable of z3.  Second, open a terminal at the
root of literate-unitb and type

	ghc test.hs -threaded
	runhaskell run_tests.hs

A series of test results should appear ending with

	***********
	* SUCCESS *
	***********

Git
===

As a rule, do not publish a commit unless (0) the tests have been run
just before the commit and (1) the tests are successful.

In order to stay up to date with the project's lead developments
(today known under the pseudonym cipher1024), enter the command:

    git remote cipher https://cipher2048@bitbucket.org/cipher2048/literate-unitb.git

then, any time you need to update one of the branches (most likely the
master branch):

    git pull cipher master

Haskell Libraries
=================

In order to compile Literate Unit-B, you need a number of Haskell
libraries which you can install using cabal in the command line.

	cabal install <lib-name>
	
The command to install the libraries is:

	cabal install either MissingH cereal ansi-terminal data-ordlist timeit zlib shelly
	
Z3
==

Z3 can be obtained from http://z3.codeplex.com/ and should be placed
in the PATH. Be sure to get version 4.3.2, hashcode 2ca14b49fe45.

Using Literate Unit-B
=====================

In a terminal, launch

	continuous -c source-file.tex

This will lauch Literate Unit-B in continuous (or interactive) mode.
As source-file.tex (or any file it inputs) gets updated, Literate
Unit-B regenerates the proof obligations and tries any new one.

The command

	continuous source-file.tex

will launch one verification and terminate.

The suggested workflow is to integrate Literate Unit-B to a LaTeX 
creation workflow and to keep the terminal in sight to see failed 
verification.
