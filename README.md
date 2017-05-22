OS X / Linux: [![Build Status](https://travis-ci.org/unitb/literate-unitb.svg?branch=master)](https://travis-ci.org/unitb/literate-unitb)

Windows: [![Build status](https://ci.appveyor.com/api/projects/status/ftkjg65dda28qir7?svg=true)](https://ci.appveyor.com/project/cipher1024/literate-unitb)

What you need to do
===================

* Get Haskell Platform
* Get Z3
* Get the Literate Unit-B source
* Compiling the utilities package
* Compiling the Unit-B program
* Run the test suite

Getting a Haskell Platform
==========================

Download the Haskell platform at https://www.haskell.org/

Z3
==

Z3 can be obtained from http://z3.codeplex.com/ and should be placed
in the PATH. Be sure to get version 4.3.2, hashcode 2ca14b49fe45.

Git
===

As a rule, do not publish a commit unless (0) the tests have been run
just before the commit and (1) the tests are successful.

In order to stay up to date with the project's lead developments
(today known under the pseudonym cipher1024), enter the command:

    > git remote cipher https://cipher2048@bitbucket.org/cipher2048/literate-unitb.git

then, any time you need to update one of the branches (most likely the
master branch):

    > git pull cipher master

Compiling the utilities
=======================

In order to compile Literate Unit-B, you need a number of Haskell
libraries which you can install using cabal in the command line.

	> cd utils
	> cabal install
	> cd ..

Compiling the Literate Unit-B Binaries
======================================

	> cabal install

Compiling and Running the Tests
===============================

First, at the root of literate-unitb, create a directory called bin
and put the binary executable of z3.  Second, open a terminal at the
root of literate-unitb and type

	> cabal run run_tests

A series of test results should appear ending with

	***********
	* SUCCESS *
	***********

Using Literate Unit-B
=====================

First off, use the `install-stylesheets-macosx.hs` script in the
[unitb/literate-unitb-scripts](https://github.com/unitb/literate-unitb-scripts)
repo to copy the required LaTeX style files to their destination.
On Linux, the destination path is `~/texmf/tex/`.

In a terminal, launch

	> unitb -c source-file.tex

This will lauch Literate Unit-B in continuous (or interactive) mode.
As source-file.tex (or any file it inputs) gets updated, Literate
Unit-B regenerates the proof obligations and tries any new one.

The command

	> unitb source-file.tex

will launch one verification and terminate.

The suggested workflow is to integrate Literate Unit-B to a LaTeX 
creation workflow and to keep the terminal in sight to see failed 
verification.

Machine Syntax
==============

Use the style-sheet unitb.sty provided in Tests/

\begin{machine}{<machine-name>}
		--
		-- Structural declaration
		--
	\refines{<machine-name>}
	\newset{<name>}
		name can be a command
	\newevent{<label>}{<displayed-name>}
		we use <label> to refer to the event when adding assignments and 
	\with{<theory>}
		available theories:
			* sets
			* functions
			* arithmetic
			* predcalc
			* intervals
		--
		-- Symbol declaration
		--
	\variable{ sym1, .., symN : Type }
		declares sym1 to symN as variables of the enclosing machine
	\constant{ sym1, .., symN : Type }
		declares sym1 to symN as variables of the context of the machine
	\dummy{ sym1, .., symN : Type }
		declares sym1 to symN as dummies and gives them types in quantifiers
		when the context does not make the type of bound variables clear
	\indices{<event-label>}{ sym1, .., symN : Type }
	\param{<event-label>}{ sym1, .., symN : Type }
		declare sym1 to symN as indices (or parameters) of event <event-label>
		--
		-- New expressions
		--
		# Context
	\assumption{<label>}{<bool-expression>}
		# Machine expressions
	\initialization{<label>}{<bool-expression>}
	\invariant{<label>}{<bool-expression>}
	\transient{<event-label>}{<label>}{<bool-expression>}
	\transientB{<event-label>}{<label>}{<hint>}{<bool-expression>}
			hints can contain:
				\index{<index>}{<expression>}
					for example \index{pid}{head.queue} would choose an
					event whose index is at the head of a queue
				\witness{<index>}{<bool-expression>}
					\witness{pid}{pid' \in free} chooses any free process
					id to falsify the transient predicate
				\lt{<prog-label>}
					When \transientB names an event with a fine schedule,
					the progress property ensures that the fine schedule 
					is true infinitely often if the transient predicate
					remains true continually.
	\constraint{<label>}{<bool-expression-with-primes>}
	\safety{<label>}{<bool-expression>}{<bool-expression>}
		\safety{lbl}{p}{q} declares the property p unless q
	\safetyB{<label>}{<event-label>}{<bool-expression>}{<bool-expression>}	
		\safetyB{lbl}{evt}{p}{q} declares the property p unless q except evt
	\progress{<label>}{<bool-expression>}{<bool-expression>}
		# Event expressions
	\evguard{<event-label>}{<guard-label>}{<bool-expression>}
	\cschedule{<event-label>}{<guard-label>}{<bool-expression>}
	\fschedule{<event-label>}{<guard-label>}{<bool-expression>}
	\evassignment{<event-label>}{<action-label>}{<boolean expression with primes>}
	\evbcmeq{<event-label>}{<action-label>}{<variable>}{<expression>}
	\evbcmsuch{<event-label>}{<action-label>}{<variable-list>}{<bool-expression-with-primes>}
	\evbcmin{<event-label>}{<action-label>}{<variable>}{<set-expression>}
		# Refinement and Proofs
	\refine{<target-prog>}{<rule-name>}{<list-of-hypothesis>}{<hints>}
	\replace{<event-label>}{<list-of-old-coarse-schedules>}{<list-of-new-coarse-schedules>}{<list-of-supporting-schedules>}{<progress-property-label>}{<safety-property-label>}
		\replace{evt}{old}{new}{supp}{prog}{saf} removes old, replace them with
		new and uses supp in the proof. prog and saf have to establish:
			old ∧ supp |-> new ∧ supp
			new ∧ supp  unless  ¬(old ∧ supp)
	\weakento{<event-label>}{<list-of-old-coarse-schedules>}{<list-of-new-coarse-schedules>}
		Deletes the old coarse schedules and replace them with the new 
		weaker ones. When designing a new scheduled event, the "default" 
		schedule, false, has to be weakened in order to apply fairness
		to the new event.
	\replacefine{<event-label>}{<old-fine-schedule>}{<new-fine-schedule>}{<optional-progress-property>}
	\removeguard{<event-label>}{<list-of-guard-labels>}
	\begin{proof}{<proof-obligation-label>}
		see the proof syntax
		# Comments
	\comment{<item>}{<string>}
		item can be the label of an invariant, a progress property, an event
		or a variable's name. The comment will be attached to the item in 
		the generated summaries.

Proof Syntax
============

In machines and theories ...

Refinement of Progress Properties
=================================

Expression Syntax
=================

Documentation Generation
========================
