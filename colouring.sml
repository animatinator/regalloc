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



(* Colouring satisfies constraints *)
val colouring_satisfactory_def = Define `
    (colouring_satisfactory col [] = T) /\
    (colouring_satisfactory col ((r, rs)::cs) = ~(MEM (col r) (MAP col rs))
    			    /\ (colouring_satisfactory col cs))
`


(* Identity colouring *)
val identity_colouring_def = Define `
    (identity_colouring constraints = \x.x)
`

(* Naive colouring *)

val naive_colouring_aux_def = Define `
    (naive_colouring_aux [] n = (\ x . n)) /\
    (naive_colouring_aux ((r, rs)::cs) n =
    			 (r =+ n) (naive_colouring_aux cs (n+1)))
`

val naive_colouring_def = Define `
    (naive_colouring constraints = naive_colouring_aux constraints 0)
`

(* Lowest-first colouring:
Take the supplied constraints in order, and assign to each register the
lowest colour which doesn't conflict *)
(* Doesn't work just now as smallest_nonmember can't be proven total *)

(*val smallest_nonmember_def = Define `
    (smallest_nonmember list x = if ~(MEM x list) then x
    			else (smallest_nonmember list (x+1)))
`

val lowest_available_colour_def = Define `
    (lowest_available_colour col cs = smallest_satisfying
        (\x . ~MEM x (MAP col cs)) 0)
`

val lowest_first_colouring_def = Define `
    (lowest_first_colouring [] = \x.0) /\
    (lowest_first_colouring ((r, rs)::cs) =
        let col = (lowest_first_colouring cs) in
	let lowest_available = (lowest_available_colour col rs)
`*)


``
!cs.colouring_satisfactory (naive_colouring cs) cs
``
Induct_on `cs`
EVAL_TAC

Cases_on `h`
EVAL_TAC
(* show colouring_satisfactory (naive_colouring_aux cs 1) cs
by implication from the assumptions (should be valid?) *)
(* show that (q =+ 0) is still satisfactory, part of goal done *)
(* need that q isn't a member of r... Make that an assumption.
Will need to prove that there are no instances of a register conflicting
with itself in the definition of get_conflicts *)
`colouring_satisfactory (naive_colouring_aux cs 1) cs` by cheat
`colouring_satisfactory ((q =+ 0) (naive_colouring_aux cs 1)) cs` by cheat
FULL_SIMP_TAC bool_ss []
`~(MEM q r)` by cheat


val naive_colouring_step = prove(``
(naive_colouring_aux ((q,r)::cs) n) = (q=+n) (naive_colouring_aux cs (n + 1))
``, FULL_SIMP_TAC std_ss [naive_colouring_aux_def])

val function_irrelevant_update = prove(``
! x list n f .
~(MEM x list) ==>
((MAP ((x=+n) f) list) = (MAP f list))
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
`~(MEM x list)` by METIS_TAC [MEM] THEN
`MAP ((x =+ n) f) list = MAP f list` by METIS_TAC [] THEN
FULL_SIMP_TAC std_ss [MAP] THEN
Cases_on `x = h` THEN1 (`MEM x (h::list)` by METIS_TAC [MEM]) THEN
FULL_SIMP_TAC bool_ss [UPDATE_def])


val colouring_map_with_unused_update = prove(``
! q r n cs .
~(MEM q r) ==>
(MAP ((q=+n) (naive_colouring_aux cs (n + 1))) r
=
MAP (naive_colouring_aux cs (n + 1)) r)
``,
REPEAT STRIP_TAC THEN
IMP_RES_TAC function_irrelevant_update THEN
METIS_TAC [function_irrelevant_update, naive_colouring_aux_def])



val naive_colouring_aux_satisfactory = prove(``
!cs n . colouring_satisfactory (naive_colouring_aux cs n) cs
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
Cases_on `h` THEN
EVAL_TAC THEN
STRIP_TAC THEN
STRIP_TAC THEN
`colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs` by METIS_TAC []
THEN cheat)
(* First subgoal is provable with colouring_map_with_unused_update, provided
the assumption ~(MEM q r) can be added (means a register does not clash with
itself and does hold of the get_conflicts implementation).
Second can't be directly proved as-is
*)


val naive_colouring_aux_satisfactory_implication = prove(``
(!cs n . colouring_satisfactory (naive_colouring_aux cs n) cs)
==> (!cs n . colouring_satisfactory (naive_colouring cs) cs)
``,
REPEAT STRIP_TAC THEN
Cases_on `cs` THEN1 EVAL_TAC THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [naive_colouring_def]
THEN cheat)
(*
    
    colouring_satisfactory (naive_colouring_aux ((q,r)::t) 0) ((q,r)::t)
    ------------------------------------
      !cs n. colouring_satisfactory (naive_colouring_aux cs n) cs
     : proof

last goal is instance of the assumption, but can't work out how to
instantiate the assumption to prove the goal
(cs = ((q,r)::t), n = 0 should work) *)