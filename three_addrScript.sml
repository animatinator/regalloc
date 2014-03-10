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
    (colouring_ok c [] live = duplicate_free (MAP c live)) /\
    (colouring_ok c ((Inst w r1 r2)::code) live =
    		  duplicate_free (MAP c (get_live ((Inst w r1 r2)::code) live))
    		  /\ colouring_ok c code live)
`


val no_dead_code_def = Define `
    (no_dead_code [] _ = T) /\
    (no_dead_code ((Inst w r1 r2)::code) live = MEM w (get_live code live)
    		  /\ no_dead_code code live)
`


(* no_dead_code is preserved by removing the first instruction *)
val no_dead_code_preserved = prove(``
    no_dead_code (Inst n n0 n1 :: code) live ==>
    no_dead_code code live``,
    RW_TAC std_ss [no_dead_code_def])

(* colouring_ok is preserved by removing the first instruction *)
val colouring_ok_preserved = prove(``
    colouring_ok c (Inst n n0 n1 :: code) live ==>
    colouring_ok c code live``,
    RW_TAC std_ss [colouring_ok_def]);

val colouring_ok_IMP_eval_apply = prove(``
   !code s t c live f.
      colouring_ok c code live /\ no_dead_code code live /\
      (MAP s (get_live code live) = MAP (t o c) (get_live code live)) ==>
      (MAP (eval f s code) live = MAP (eval f t (apply c code) o c) live)``,
  Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC)
  THEN FULL_SIMP_TAC std_ss []
  THEN REPEAT STRIP_TAC
  THEN Cases_on `h`
  THEN SIMP_TAC std_ss [apply_def,eval_def]
  THEN IMP_RES_TAC no_dead_code_preserved
  THEN IMP_RES_TAC colouring_ok_preserved
  THEN FIRST_X_ASSUM MATCH_MP_TAC
  THEN FULL_SIMP_TAC std_ss [MAP_EQ_f,APPLY_UPDATE_THM]
  THEN FULL_SIMP_TAC std_ss [get_live_def,MEM_insert,MEM,delete_def,MEM_FILTER]
  THEN REPEAT STRIP_TAC
  THEN REVERSE (`(c n = c e) = (n = e)` by ALL_TAC)
  THEN1 FULL_SIMP_TAC std_ss []
  THEN Cases_on `n = e` THEN FULL_SIMP_TAC std_ss []
  THEN FULL_SIMP_TAC std_ss [no_dead_code_def, colouring_ok_def]
  THEN IMP_RES_TAC colouring_ok_injective)


val colouring_ok_injective = prove(``
    ! c code live x y .
      (no_dead_code code live) /\
      (colouring_ok c code live) /\ ~(x = y) /\
      (MEM x (get_live code live)) /\ (MEM y (get_live code live))
    ==> ~(c x = c y)
``,
REVERSE (Induct_on `code`)
THEN1 (REPEAT STRIP_TAC
THEN Cases_on `h`
THEN1 (IMP_RES_TAC colouring_ok_preserved
THEN IMP_RES_TAC no_dead_code_preserved
THEN cheat))

THEN1 (
EVAL_TAC
THEN Induct_on `live`
THEN1 (EVAL_TAC THEN DECIDE_TAC)
THEN1 (REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [MAP, duplicate_free_def]
THEN Cases_on `x = h`
THEN1 (`~(y = h)` by METIS_TAC [] 
THEN `MEM y live` by FULL_SIMP_TAC std_ss [MEM]
THEN `MEM (c y) (MAP c live)` by METIS_TAC [MEM, MAP, MEM_MAP]
THEN `~(MEM (c x) (MAP c live))` by METIS_TAC []
THEN `~(c x = c y)` by METIS_TAC [])
THEN1 (
      Cases_on `y = h`
      THEN1 (`~(x = h)` by METIS_TAC []
      THEN `MEM x live` by FULL_SIMP_TAC std_ss [MEM]
      THEN `MEM (c x) (MAP c live)` by METIS_TAC [MEM, MAP, MEM_MAP]
      THEN `~(MEM (c y) (MAP c live))` by METIS_TAC []
      THEN `~(c x = c y)` by METIS_TAC [])
      THEN1 (`MEM x live` by METIS_TAC [MEM]
      THEN `MEM y live` by METIS_TAC [MEM]
      THEN `~(c x = c y)` by METIS_TAC [])
      )
)))


(* attempting the other way around *)
val mem_after_map = prove(``! x xs (c:num->num) .
    MEM x xs ==> MEM (c x) (MAP c xs)``,
RW_TAC std_ss [MEM_MAP] THEN Q.EXISTS_TAC `x`
THEN EVAL_TAC THEN FULL_SIMP_TAC bool_ss [])


``
    ! (c:num->num) code live x y .
      (no_dead_code code live) /\
      (colouring_ok c code live) /\ (c x = c y) /\
      (MEM x (get_live code live)) /\ (MEM y (get_live code live))
    ==> (x = y)
``
Induct_on `code`
EVAL_TAC
REPEAT STRIP_TAC
IMP_RES_TAC mem_after_map
`MEM (c x) (MAP c live)` by FULL_SIMP_TAC std_ss []
FULL_SIMP_TAC std_ss [MEM_MAP] (* ? *)


val _ = export_theory();
