open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory;


(* get the list of pairs which mustn't be assigned the same colour *)
val get_conflicts_def = Define `
    (get_conflicts [] live x y = x <> y /\ (MEM x live) /\ (MEM y live)) /\
    (get_conflicts ((Inst r0 r1 r2)::code) live x y =
    		     x <> y /\
		     (MEM x (get_live ((Inst r0 r1 r2)::code) live)
		     /\ MEM y (get_live ((Inst r0 r1 r2)::code) live))
		     \/ (get_conflicts code live x y)
    )
`

(* prove that a colouring obeying the constraints is a valid colouring *)
val get_conflicts_colouring_ok = prove(``
    !c code live .
    duplicate_free live /\
    (! x y . (get_conflicts code live) x y ==> c x <> c y)
       ==> (colouring_ok c code live)``,
Induct_on `code`
THEN RW_TAC bool_ss [get_conflicts_def, colouring_ok_def]
THEN Cases_on `live`
EVAL_TAC
cheat
(*inductive now *)
REPEAT STRIP_TAC
`! x y . get_conflicts code live x y ==> c x <> c y` by ALL_TAC
REPEAT STRIP_TAC
`get_conflicts (h::code) live x y` by ALL_TAC
Cases_on `h`
RW_TAC bool_ss [get_conflicts_def]
METIS_TAC []
`colouring_ok c code live` by METIS_TAC []
Cases_on `h`
RW_TAC bool_ss [colouring_ok_def, get_live_def, MAP]
(* stuck *)


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


(* prove the basic algorithm is correct in the absence of prior live
variables *)
val basic_colouring_ok = prove(``
    !code . colouring_ok (basic_colouring code) code []``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC)
THEN RW_TAC bool_ss [basic_colouring_def]
THEN Cases_on `h`
THEN RW_TAC bool_ss [get_registers_def]
THEN cheat)
(* WIP - awkward to prove with the three inserts at the moment, may need a
different approach *)


(* Very simplified naive colouring proof *)
val identity_colouring_ok = prove(``!code . colouring_ok (\x . x) code []``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC)
THEN Cases_on `h`
THEN RW_TAC bool_ss [colouring_ok_def, get_live_def, map_identity]
THEN RW_TAC bool_ss [duplicate_free_insertion, duplicate_free_deletion]
THEN `duplicate_free ([]:num list)` by EVAL_TAC
THEN METIS_TAC [get_live_has_no_duplicates])