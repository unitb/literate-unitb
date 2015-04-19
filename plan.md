Todo:
	documentation for syntax and options

    * ~~sum~~
    * data refinement
        * ~~test: the set of remaining actions after data refinement~~

        * (∀v,w,w': cAct(w,w') ∧ J(v,w): (∃v':: aAct(v,v') ∧ J(v',w')))
            * witness
                * ~~infer witnesses from BA pred~~
                * ~~WD of witnesses separately from FIS~~
                * check scope: the free variables should be concrete variables plus a certain deleted variable
            * ~~simulation PO~~
        * ~~Commit~~

        * ~~removal of inital condition~~
        * ~~Witness / sim of init removal~~
        * ~~Problem: name clash between witnesses of events vs init~~
        * ~~commit~~

        * ~~Add error message when~~
            * ~~deleting non existing~~
                * ~~action / init~~
                * ~~variable~~
            * ~~providing witness for variable that isn't deleted~~
        * ~~In phase 2, variable collection,~~
            * ~~define the missing process decl~~
            * ~~construct a notation object and some parsers~~
        * ~~commit~~

        * ~~aggregate expr scopes before adding in parser~~
        * commit

        * typesetting example
        * refactor: split UnitB.AST into Event and Machine
        * refactor: rename MachinePh into MachineP and EventPh into EventP
        * commit
        
        * Turn EventId into (EventId s) in order to make tables of
            events into total functions

        * reformulate schedule refinement with the new deletion mechanism
        * Question: Is it valid to define new invariants / transient predicates referring to deleted variables after the completion of the removal of said variables?
            * tentative answer: no
        * Error message when schedule or guard refers to deleted variables
        * test: the set of remaining guards, coarse, fine schedules after data refinement
    * puzzle

    * shared variable decomposition
    * finite and subset with instantiation pattern
    * context
    * event splitting / merging
    * feasibility should be tested only once 


* Literate Unit-B
    * Make it possible to refine without explicitly calling on refinement rules
        * just using cschedule{..} could be enough .. (at least for the first model)
    * Distinguish between spontanous events and schedules events
        * Scheduled events have the same guard and schedules
    * ~~build operator abstractions~~
        * in order to introduce regularity calculus and relational calculus
    * machines
        * halt events
        * add a syntax for specifying a progress property with ... ?
    * theories
        * real-time
        * theorems
        * custom proof rules
            * ~~indirect inequality~~
            * proof tactics
        * relevance filters
        * import errors?
        * refinement of theories and algebraic structures (partial orders, groups, monoid, etc)
        * relational theory
        * custom quantifiers
    * design
        * soft failures vs hard failures in parser
        * file watcher in pipeline for multifile documents
        * introduce the production of system summary to the pipeline
            * include the production of ~~invariant listings~~ and proof obligations
        * change the implementation of label to allow LaTeX rendering (with proofs)
    * bug: 
        * when using dummies without quantifiers, there should be an error message
        * \replace and \replacefine use inconsitent convention: unify and have the LaTeX package print the details
    * example: 
        Wim Feijen exercises on predicate calculus, partial orders, lattices and galois connections
    * ~~introduce "_ unless _ except _"~~
    * find out if cyclic reasoning involving schedules get detected
        * coarse schedule replacement cannot rely on progress properties defined in ancestors
    * Axes of extension
        * ease of adding features like code generation, summary generation, proof obligation generation 
        * ease of adding language features like invariants, proofs, actions, etc
    * types and logic
        * ~~inference of generic parameters~~
        * type check index hints
        * dimensional analysis
        * new lambda formalization to separate range and term
    * add the file name in the error messages
    * allow cross referencing with proof obligations and events / properties
    * GUI (browser)
    * WD and 〈 • 〉 and [ • ]
* Unit-B examples
    * Tank (real time, continuous component, imprecise measurement)
    * SCC (sequential programs, anticipated properties, relational calculus)
    * Dining philosophers (anticipated properties)
    * Routing
* Unit-B GUI views
    * Sublime Text package
    * Failed POs view
        * tree view: open up to see 
    * syntax errors
    * sections and machines
        * tree view: open up to see: invariants, events, variables
Unit-B
    * ~~improve build system performance~~
    * move sources into an src folder
    * improve pretty_print
    * conditional transient 
        * \transient{tr0}{ p }{ evt1[i := x], evt2[j := y] }
            evt1 [i]
                during c0
                upon f0
                do A0
                end
            evt2 [j]
                during c1
                upon f1
                do A1
                end
            (∃i:: EN0.i ∧ NEG0.i ∧ FOLLOW0.i)
            (∃j:: EN0.j ∧ NEG0.j ∧ FOLLOW0.j)
            (EN)     p ⇒ c0.x
            p ⇒ c1.y
            (NEG)    { p ∧ c0.x ∧ f0.x } A0.x { ¬p } 
            { p ∧ c1.y ∧ f1.y } A1.y { ¬p }
            (FOLLOW)    p ∧ c0.x ∧ c1.y ↦ f0.x ∨ f1.y 
            or   p ∧ c0.x ∧ c1.y  ⇒  f0.x ∨ f1.y
        * write test checking the full proof obligation
        * in \refine{ensure} and \refine{discharge}, \index{r}{z+x}, add a mention of the events
    * ~~documentation (variables)~~
    * ~~\comment{var | event | action | prop | inv}~~
    * "becomes equal to" and event frames
        * ~~simulation and EQL proof obligation~~
        * ~~WD PO: only new actions~~
        * FIS PO: only the "becomes such that” actions need to be considered unless the primed variable of an assignment is mentioned
        * f(x) := f(y), f(y) := f(x) -> f := f | x → f.y | y → f.x
    * prefix commands with M (or T) and environments with M: (or T:)
    * ~~disconnect schedule and events~~
        * add conditional transient
        * add event splitting
        * \skip{x,y} notation in proof hints
    * event (and variable) groups (a la Eiffel) to clarify documentation
* typing
    use relations in calculations to infer types of steps
* Doc generation
    generate lists of variables
    properties and invariants
* code generation
    1. assign sets of events to code fragments
    2. given an event, a code fragment (sequence, iteration (while, foreach), conditional)
        1. fragment executes the event at least once
        2. fragment executes the event repeatedly
        3. does the event occur for as long as the fragment runs
        4. does the fragment prevent the event from occurring infinitely many times?
        5. Is the fragment guaranteed to terminate?
            :   for loops, attach a progress property backed by separate events or by events occurring continuously in the loop.
 * Random testing of concurrent programs
* subtyping
    structure preserving functions through locales 
    classes as implicit locales
* Z3: Explicitly instantiate the universal quantifications with first generation expressions of the right type hence making the PO quantifier free and facilitating the decision of proof steps.
* syntactic properties (commutativity, associativity, monotonicity):
    * should be accessible in all proofs of the same theory except for the proofs of theorems supporting the syntactic property
    * have a datatype 
        data SyntacticProp = 
            Assoc Fun | Comm Fun 
            | Mono Fun ExprZipper Fun 
        with the meaning of Mono r0 f r1 that function f translates relation r1 into r0  
* new function rules:
    s₀ ⊆ ran.(s₁ <<| f)  ⇐  s₀ \ ran.(s₁ ◁ f) ⊆ ran.f
    s₀ \ f[ s₁ ] ⊆ ran.f
    s₀ ⊆ ran.(s₁ ◁ f)  ⇐  s₀ \ ran.(s₁ <<|  f) ⊆ ran.f

    ran.(f | x→ y)  =  ran.({x} <<| f) ∪ {y}
* proof rules
    * implicit assumptions (that are used for proof steps whether or not they are referenced in the hints)
    * easy assertion / assertions that make the goal easy, mentioned in hints
    * new names
* range and domain restriction / subtraction
* usability
    * documentation
        * output proof obligations with command: \po
        * invariants
    * goto definition: list event components and jump to each
    * add a focus to the display of failed proofs
    * detect whether all events (and init) assign to all variables
    * unitb.sty: allow \evassignment{evt1,evt2} …
    * prefix all the commands and environment for machines with M and all the commands and environment for contexts with T in order to detect invalid commands
    * plugin with Sublime Text
    * adding a schedule should add a guard
    * find a short-hand for long leads-to and unless properties
        p ↦ q would stand for D(p) ∧ p  ↦  D(q) ∧ q
* Error: only one refinement should be possible per property
* theory and rules
    * leads-to property with events:
        * p ↦ evt ∧ q via ensures p ⇒ sch of evt, { p } evt { q } and p is stable in the rest of the program
        * evt ∧ p ↦ q via ensures { evt_grd } evt { p ⇒ q }
    * function, variable definitions in Unit-B
        * by equation (proof of existence)
        * provide precondition
            f.x.y.z = E
            provided P
            -->
            (∀x:: x ∈ dom.f)
            (∀x,y:: y ∈ dom.(f.x))
            (∀x,y:: z ∈ dom.(f.x.y) ≡ P)
            (∀x,y :: f.x.y.z = E)
* weird crashes of the prover when working with lock-free: create a log of exceptions thrown by the prover
* Lock-free
    main5 should have a syntax error because I weaken the same schedule twice
* have a more modular error system
    take the error messages out of the parsing code
* QuickCheck
    * Machine
        type errors involving polymorphic types 
        scope errors
    * random n-ary trees as a basis for general recursive data structures
    * expressions
    * tactics
    * refinement
* Isabelle proofs for
    * a watch dog for proof trees
    * Unit-B proof obligation generator
    * basic proof tactics (quickCheck can already help)
    * expression parser