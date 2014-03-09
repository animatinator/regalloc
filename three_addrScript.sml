open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory;

val _ = new_theory "three_addr";

(* type of instruction *)

val _ = Hol_datatype `
  inst = Inst of num => num => num `

(* type of colouring *)

val _ = Hol_datatype `
  colouring = Col of num => num`

(* semantics of instruction evaluation *)

val eval_def = Define `
  (eval f s [] = s) /\
  (eval f s ((Inst w r1 r2)::code) =
     eval f ((w =+ f (s r1) (s r2)) s) code)`;

(* apply a colouring to a set of instructions *)
val apply_def = Define `
    (apply c [] = []) /\
    (apply c ((Inst w r1 r2)::code) = (Inst (c w) (c r1) (c r2))::(apply c code))
`

(* helper functions *)

val insert_def = Define `
  insert x xs = if MEM x xs then xs else x::xs`;

val delete_def = Define `
  delete x xs = FILTER (\y. x <> y) xs`;

(* proofs about helper functions *)
val insert_mapping = prove(
  ``(MAP s (insert x list) = MAP t (insert x list)) ==>
  (MAP s list = MAP t list)``,
  RW_TAC bool_ss [insert_def, MAP])



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

val MEM_inserted_item = prove(``MEM x (insert x xs)``, SIMP_TAC std_ss [MEM_insert, MEM]);

val MEM_after_insertion = prove(``MEM x xs ==> MEM x (insert y xs)``, SRW_TAC [] [insert_def]);


val eval_get_live = prove(
  ``!code s t live f.
      (MAP s (get_live code live) = MAP t (get_live code live)) ==>
      (MAP (eval f s code) live = MAP (eval f t code) live)``,
Induct_on `code`
(* base case *)
THEN1 (EVAL_TAC THEN SIMP_TAC std_ss [])

(* inductive case *)
THEN1 (
  Cases_on `h` THEN  (* expand h *)
  FULL_SIMP_TAC std_ss [get_live_def, insert_mapping, eval_def] THEN
  REPEAT STRIP_TAC THEN
  
  (* The following implies the goal using the inductive hypothesis *)
  ` MAP ((n =+ f (s n0) (s n1)) s) (get_live code live)
    = MAP ((n =+ f (t n0) (t n1)) t) (get_live code live)` by ALL_TAC
  THENL [
    `MAP s (delete n (get_live code live))
      = MAP t (delete n (get_live code live))`
    by METIS_TAC [insert_mapping] THEN
    FULL_SIMP_TAC std_ss [delete_def, MAP_EQ_f, MEM, MEM_FILTER] THEN
    REPEAT STRIP_TAC THEN
    EVAL_TAC THEN
    Cases_on `n = e` THENL [
      ASM_SIMP_TAC bool_ss [COND_CLAUSES] THEN
      `MEM n0 (insert n0 (insert n1
        (FILTER (\y . ~(n = y)) (get_live code live))))
        /\ MEM n1 (insert n0 (insert n1
      	(FILTER (\y . ~(n = y)) (get_live code live))))`
      by ALL_TAC

      THENL [
        `!xs . MEM n0 (insert n0 xs)` by METIS_TAC [MEM_inserted_item] THEN
        FULL_SIMP_TAC bool_ss [] THEN
        `!xs . MEM n1 (insert n1 xs)`
          by METIS_TAC [MEM_inserted_item, MEM_after_insertion] THEN
        METIS_TAC [MEM_after_insertion],
        METIS_TAC []
      ],
      
    ASM_SIMP_TAC bool_ss [COND_CLAUSES]
    ],
      
  METIS_TAC []
  ]
)
);



val duplicate_free_def = Define `
    (duplicate_free [] = T) /\
    (duplicate_free (x::xs) = ~(MEM x xs) /\ duplicate_free xs)
`

val colouring_ok_def = Define `
    (colouring_ok c code live = duplicate_free (MAP c (get_live code live)))
`


val no_dead_code_def = Define `
    (no_dead_code [] _ = T) /\
    (no_dead_code ((Inst w r1 r2)::code) live = MEM w (get_live code live)
    		  /\ no_dead_code code live)
`


val duplicate_free_map = prove(
``
duplicate_free (MAP c list) ==> duplicate_free (list)
``,
REPEAT STRIP_TAC THEN
Induct_on `list` THEN1 (
EVAL_TAC)
THEN1 (
STRIP_TAC THEN
STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [MAP] THEN
`duplicate_free (MAP c list)` by (FULL_SIMP_TAC bool_ss [duplicate_free_def]) THEN
`duplicate_free list` by METIS_TAC [] THEN
FULL_SIMP_TAC bool_ss [duplicate_free_def] THEN
Cases_on `MEM h list` THEN1 (
FULL_SIMP_TAC bool_ss [MEM] THEN
cheat) (* todo - is sort-of trivial but hard *)
THEN1 (METIS_TAC [])))


(* Lemma for the below, need to do something for deletion too *)
val duplicate_free_map_insertion = prove(``
    duplicate_free (MAP c (insert n x)) ==>
    duplicate_free (MAP c x)
``,
EVAL_TAC THEN STRIP_TAC THEN Cases_on `MEM n x`
THEN1 (FULL_SIMP_TAC bool_ss [])
THEN1 (FULL_SIMP_TAC bool_ss []
      THEN FULL_SIMP_TAC bool_ss [MAP, duplicate_free_def]))

(* need this to obtain `colouring_ok c code live` for the proof later *)
``
no_dead_code (Inst n n0 n1 :: code) live /\
colouring_ok c (Inst n n0 n1 :: code) live ==>
colouring_ok c code live
``
SIMP_TAC bool_ss [colouring_ok_def]
SIMP_TAC bool_ss [get_live_def]
STRIP_TAC
`duplicate_free (MAP c (delete n (get_live code live)))`
by METIS_TAC [duplicate_free_map_insertion]
FULL_SIMP_TAC bool_ss [delete_def]
(* TODO looks true but need to remove the `delete n`... *)



(* no_dead_code is preserved by removing the first instruction *)
val no_dead_code_preserved = prove(``
    no_dead_code (Inst n n0 n1 :: code) live ==>
    no_dead_code code live``,
    RW_TAC std_ss [no_dead_code_def])


``
 !code s t c live f.
    colouring_ok c code live /\ no_dead_code code live /\
    (MAP s (get_live code live) = MAP (t o c) (get_live code live)) ==>
    (MAP (eval f s code) live = MAP (eval f t (apply c code) o c) live)
``
Induct_on `code`
EVAL_TAC THEN DECIDE_TAC

FULL_SIMP_TAC std_ss []
REPEAT STRIP_TAC
Cases_on `h`
EVAL_TAC
(* plan: use the inductive lemma with appropriate substitutions for s and t.
This will require transforming the conditions colouring_ok, no_dead_code etc.
which work on (Inst n n0 n1 :: code) into ones working on code alone. *)


(* Other proof idea: use eval_get_live?
Gives us MAP (eval f s code) live = MAP (eval f (t o c) code) live
Can the RHS of that be rewritten to MAP (eval f t (apply c code) o c) live
as needed?
We have that c is ok so applying c to live doesn't conflate things
Looking at definitions of eval and apply, it looks like the equality should
be valid maybe *)

(* attempting the rewrite needed *)
``
! t c live f.
MAP (eval f (t o c) code) live = MAP (eval f t (apply c code) o c) live
``
Induct_on `code`
EVAL_TAC
DECIDE_TAC
Cases_on `h`
RW_TAC bool_ss [apply_def]
RW_TAC bool_ss [eval_def]
(* This looks potentially right. Need to rearrange the ((n =+ blah) o (t o c))
to a modification of t compatible with the one it needs to be equal to so we
can use the inductive hypothesis.
Would be roughly this:
(c n =+ x) (t o c) = ((n =+ x) t) o c
*)

``
! c n x t .
(c n =+ x) (t o c) = ((n =+ x) t) o c
``
RW_TAC bool_ss [o_DEF]
RW_TAC bool_ss [UPDATE_def]
(* Have to prove the functions are equal - can this be broken down into showing
they're equal for an arbitrary argument? *)

val _ = export_theory();
