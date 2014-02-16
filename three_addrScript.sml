open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory;

val _ = new_theory "three_addr";

(* type of instruction *)

val _ = Hol_datatype `
  inst = Inst of num => num => num `

(* semantics of instruction evaluation *)

val eval_def = Define `
  (eval f s [] = s) /\
  (eval f s ((Inst w r1 r2)::code) =
     eval f ((w =+ f (s r1) (s r2)) s) code)`;

(* helper functions *)

val insert_def = Define `
  insert x xs = if MEM x xs then xs else x::xs`;

val delete_def = Define `
  delete x xs = FILTER (\y. x <> y) xs`;

(* annotate code with live ranges *)

val get_live_def = Define `
  (get_live [] live = live) /\
  (get_live ((Inst w r1 r2)::code) live =
     insert r1 (insert r2 (delete w (get_live code live))))`;

(* test *)

val test = EVAL ``get_live [Inst 1 2 3; Inst 0 1 2] [0]``

(* only live variables matter *)

val MEM_insert = prove(
  ``MEM x (insert y ys) = MEM x (y::ys)``,
  SRW_TAC [] [insert_def] THEN METIS_TAC []);

``
!code s t live f .
      (MAP s (get_live code live) = MAP t (get_live code live)) ==>
      (MAP (eval f s code) live = MAP (eval f t code) live)
``

(* Magnus: I packaged up the base-case proof into a THEN1. THEN1 is
   very useful and much better than THENL (I guess I should update the
   little guide that I wrote http://www.cl.cam.ac.uk/~mom22/HOL-interaction.pdf). *)

Induct_on `code`
THEN1 (* base case *) (EVAL_TAC THEN SIMP_TAC std_ss [])

(* Magnus: You don't want to Induct_on `live`, because the definitions
   don't recurse on this argument. How about doing Cases_on `h` to
   expand h and then rewrite with the definition of eval and get_live
   as follows? *)

Cases_on `h`
THEN FULL_SIMP_TAC std_ss [eval_def,get_live_def]

(* Magnus: I suggest you continue by using some combination of tactics like:

              FULL_SIMP_TAC std_ss []
              REPEAT STRIP_TAC
              Q.PAT_ASSUM `!s t. bbb` MATCH_MP_TAC
              Cases_on `n = e`

           and theorems like

              MAP_EQ_f, APPLY_UPDATE_THM, MEM_insert, MEM

           and look for other theorems using

              print_match [] ``MEM y (FILTER P ys) = anything``

*)

(*

(* inductive case *)
Induct_on `live`  (* not sure if this is the right approach - seems useful
	  	  in that it makes it possible to unfold the MAP definition
		  but I get stuck trying to prove the inductive case
	  (* base case *)
	  RW_TAC bool_ss [MAP]
	  (* inductive case *)
	  RW_TAC bool_ss [MAP]
	  	 EVAL_TAC
		 Induct_on `h'`
		 RW_TAC bool_ss [MAP]
		 (* not sure how to make use of the original inductive
		 hypothesis here - have tried showing that
		 (MAP s (get_live code live) = MAP t (get_live code live))
		 and then deriving
		 (MAP (eval f s code) live = MAP (eval f t code) live)
		 which should be useful in proving the goal, but keep getting
		 mismatches between quantified and unquantified variables
		 *)

*)

(*
val it =

    eval f s (Inst n n0 n1::code) h = eval f t (Inst n n0 n1::code) h
    ------------------------------------
      0.  !s t live f.
            (MAP s (get_live code live) = MAP t (get_live code live)) ==>
            (MAP (eval f s code) live = MAP (eval f t code) live)
      1.  !h s t f.
            (MAP s (get_live (h::code) live) =
             MAP t (get_live (h::code) live)) ==>
            (MAP (eval f s (h::code)) live = MAP (eval f t (h::code)) live)
      2.  MAP s (get_live (Inst n n0 n1::code) (h::live)) =
          MAP t (get_live (Inst n n0 n1::code) (h::live))
*)


val eval_get_live = prove(
  ``!code s t live f.
      (MAP s (get_live code live) = MAP t (get_live code live)) ==>
      (MAP (eval f s code) live = MAP (eval f t code) live)``,
  cheat (* David, can you try to prove this? i.e. remove the cheat *) );

val _ = export_theory();
