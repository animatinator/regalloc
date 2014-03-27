open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory;


(* get the list of pairs which mustn't be assigned the same colour *)
val getConflicts_def = Define `
    (getConflicts [] live x y = ~(MEM x live) \/ ~(MEM y live)) /\
    (getConflicts ((Inst r0 r1 r2)::code) live x y =
		     (~(MEM x (get_live ((Inst r0 r1 r2)::code) live))
		     \/ ~(MEM y (get_live ((Inst r0 r1 r2)::code) live)))
		     /\ (getConflicts code live x y)
    )
`

(* prove that a colouring obeying the constraints is a valid colouring *)
``
!c code live .
(! x y . (getConflicts code live) x y
==>
c x <> c y)
==>
(colouring_ok c code live)
``
(* todo *)


(* very basic colouring algorithm *)
(* get the set of registers used by a section of code *)
val get_registers_def = Define `
    (get_registers [] = []) /\
    (get_registers ((Inst w r1 r2)::code) =
    		   insert w (insert r1 (insert r2 (get_registers code))))
`

(* generate a colouring assigning different values to every element of the
supplied array *)
val build_basic_colouring_def = Define `
    (build_basic_colouring i [] = (\x.0)) /\
    (build_basic_colouring i (reg::regs) =
    			   (reg =+ i) (build_basic_colouring (i+1) regs))
`

(* generate a colouring assigning different values to every register used by
a section of code *)
val basic_colouring_def = Define `
    (basic_colouring code = build_basic_colouring 0 (get_registers code))
`