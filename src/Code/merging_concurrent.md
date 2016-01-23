<!-- MarkdownTOC -->

- Goals
- Automated Partitioning of Variables and Events
- Automated Construction of Control Flow Graphs
- Verifying the Control Flow Graphs
- Removing of Auxiliary Variables
- Specifying an Implementation

<!-- /MarkdownTOC -->


## Goals

The implementation must
:	* Partition the events between processes
	- Produce a (correct) control flow graph for each process
	* Choose which guards are evaluated and which ones are not
	* Choose which variables are stored in memory and which ones are not
	* Provide executable code to evaluate guards and simulate events

## Automated Partitioning of Variables and Events

Possible Input:
  * Set of acceptable synchronized events
  * Set of shared / private / auxiliary variables

### Partitioning by Shared Variables

 1. Make a graph events as vertices 
 2. Link events that refer to the same private variables
 3. Calculate the connected components
 4. Each set of events is a process

### Partitioning by Synchronized Events
	(to be continued)
 1. Make a graph with non-synchronized events as vertices
 2. Link events that refer to the same variables
 3. Calculate the connected components
 4. Each component is the set local events of a process
 5. The set of private variable of each 

## Automated Construction of Control Flow Graphs

 * Break down schedules into atomic conjuncts and their negation
 * Form a predicate lattice
 * Predicate graphs 
 	1. link two predicates if they share a clause which is negated in one and not the other
 	2. link two predicates if they do not share an opposite clause but share other clauses
 * Test stable predicates
	 * predicate involving only local variables are trivially stable
	 * test ahead of time or upon necessity?
 * Make a bipartite graph with events and predicates
	 * evt → P: { sch } evt { P }
	 * P → evt: sch ⇒ P or P ⇒ ¬sch
	 * (Hoare graph)
 * Make and merge sequences
	 * G₀ → evt₀ { P₁ } G₁ → evt₁
	 	- { G₀ } evt₀ { P₁ }
 	 * the above with G₂ → evt₂ 

## Verifying the Control Flow Graphs
### Definitions

Precondition:
:	The events are partitioned between processes

Categories
:	* Event
	* Assertion
	* Sequence
	* Loop
		* Infinite loop
		* Finite loop
		* Wait
	* Conditional

Program fragment properties:	

  1. Correctness (mendatory)
  2. Termination (optional)
	  * Might not be needed except as a specfic property of loops	
  3. Events (set of events)
	  1. Possibly run
	  2. Certainly run
  4. Proving postconditions

A program fragment can also implement the fair scheduling

### Event Syntax

For event 'evt'

	evt
		during sch
		when   grd
		then   A
		end

Program:

	{ P }
	[ W ] G → A

with
:	* P: preassertion
	* G: guard 
	* W: waiting condition
	* A: action

<!-- Todo:
   * Check special cases (true/false) for P, G and W.
 -->
Properties:

 1. This program does not hang (and therefore is terminating) if:
	 * P ∧ ¬ W ⇒ < conjunction of 
		 < negation of each of the other schedules of the process > >
	 * (this should be correctness)
 2. This program is correct if:
	 * P is stable 
		 (in the other processes)
	 * P ∧ sch ⇒ G ∧ W
	 * P ∧ G ∧ W ⇒ grd
 3. Events
	 1. Certainly {evt}
	 2. Possibly {evt}
 4. Postcondition Q
	 * { grd } A { Q }

#### Special Case: Negative Event

Program:

	{ P }
	skip

Properties:

  1. Does not hang
  2. Correctness:
	 * P is stable
		 (in other processes)
	 * P ⇒ ¬ sch
  3. Events:
	  1. Certainly {evt}
	  2. Possibly ⌀

### Sequence Syntax

Input:

	{ P }
	prgm0

	{ Q }
	prgm1

Output:

	{ P }
	prgm0
	{ Q }
	prgm1

  1. Termination: prgm0 and prgm1 terminate
  2. Correctness
	   prgm0 { Q }
  3. Events
	  * Certainly: certain prgm0 ∪ certain prgm1
	  * Possibly:  possibly prgm0 ∪ possibly prgm1
  4. Postcondition R
	  * prgm1 { R }

### Loop Syntax

Input:
:	{ P ∧ C }
	prgm0
	{ P ∧ ¬C }
	prgm1

Output:
:	{ P }
	while C do
		{ P ∧ C }
		prgm0
	end
	{ P ∧ ¬ C }
	prgm1

Properties:

 1. Termination:
	 * One (certain) event in prgm0 decreases a variant v. It does not have a condition
	 * v ≤ V is stable
		 (in all possible events of the loop)
	 * v ≤ V is stable 
	 	 (in all the events of the other processes)
 2. Correctness:
	 * { P ∧ C } prgm0 { P }
	 * Either 
		 * Termination or
		 * The events certainly run in prgm0 = all the events of the process
 3. Events:
	 * Certainly the certain events of prgm1
	 * Possibly the possible events of prgm0 ∪ the possible events of prgm1
 4. Postcondition Q
	 * prgm1 { Q }

#### Special Case: Wait Statement

Program:

	{ P }
	wait C




### Conditional Syntax

Input:

	{ P ∧ C }
	prgm0

	{ P ∧ ¬C }
	prgm1

Output:

	{ P }
	if C then
		prgm0
	else
		prgm1
	fi

 1. Termination: 
	 * prgm0 terminates and prgm1 terminates
 2. Correctness: true
 3. Events:
	 * Certainly: (certain prgm0) ∩ (certain prgm1)
	 * Possible:  (possibly prgm0) ∪ (possibly prgm1)
 4. Postcondition Q
	 * prgm0 { Q }
	 * prgm1 { Q }

<!-- ## Merging Rules

sequence
(locally) terminating loop
<!-- merge terminating loop -->
non-terminating loop
conditional

### Old approach
#### Sequence

	evtA
		during P0 ∧ C0
		then B0
		end
 	
	evtB
		during P1 ∧ C1
		then B1
		end

===>

	evtAB
		during P0 ∧ (C0 ∨ C1)
		then 
			C0 → B0
			{ P1 }
			C1 → B1
		end

	where
		{ C0 ∧ P0 } B0 { P1 }
		P0 ∧ ¬C0 ⇒ P1
		P1 ∧ C1  unless  ¬P0 ∨ ¬C0
			(in other processes)

#### Introduce Terminating Loop

	evtA
		during P0 ∧ W0 ∧ C0
		then B0
		end

	evtB
		during P0 ∧ ¬C0
		then B1
		end

	loop
		during P0
		then 
			while C0 do
				{ P0 }
				wait W0 ∨ ¬C0
				B0
			end ;
			B1
		end

	with
		provided P0 and C0, B0 decreases a variant
			(none of the other processes increase that variant)
		{ P0 ∧ C0 } B0 { P0 }
		P0 ∧ C0 is stable 
			(in other processes)
		P0 ∧ ¬ C0 is stable 
			(in other processes) -->
## Removing of Auxiliary Variables

Input:
:	X, the set of auxiliary variables

Validity:
:	for y a non-auxiliary variable
	y := f.x 	 is not allowed
	g.x → y := E is not allowed
	g.x → x := E is allowed

## Specifying an Implementation

### Eval
  (x ∪ y) = M.union x y

### Transfer Events

  * x is external
  * do x <- readX
       use x

### CFG

   while c + b ≤ k do
   	  evtA
   	  [ b ∨ a ]
   	  g → evtB
   	  not evtC
   invariant P
   variant
   	  v by evtA
   end ;
   evtD

