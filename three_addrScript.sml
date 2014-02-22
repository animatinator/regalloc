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

val _ = export_theory();
