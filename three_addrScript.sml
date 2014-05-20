open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory rich_listTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory;

val _ = new_theory "three_addr";

(* type of instruction *)

val _ = Hol_datatype `
  op = Op of num->num->num | Move`

val _ = Hol_datatype `
  instr = Instr of op => num => num => num`

val _ = Hol_datatype `
  inst = Inst of num => num => num`

(* semantics of instruction evaluation *)

val eval_def = Define `
  (eval f s [] = s) /\
  (eval f s ((Inst w r1 r2)::code) =
     eval f ((w =+ f (s r1) (s r2)) s) code)`;

val eval_op_def = Define `
  (eval_op (Op f) = f) /\
  (eval_op (Move) = (\x1 x2 . x1))`

val eval_instr_def = Define `
  (eval_instr s [] = s) /\
  (eval_instr s ((Instr op w r1 r2)::code) =
     let f = (eval_op op) in
       eval_instr ((w =+ f (s r1) (s r2)) s) code)`;

(* apply a colouring to a set of instructions *)
val apply_def = Define `
    (apply c [] = []) /\
    (apply c ((Inst w r1 r2)::code) = (Inst (c w) (c r1) (c r2))
    	   ::(apply c code))`

val apply_instr_def = Define `
    (apply_instr c [] = []) /\
    (apply_instr c ((Instr op w r1 r2)::code) = (Instr op (c w) (c r1) (c r2))
    	   ::(apply_instr c code))`

(* helper functions *)

val insert_def = Define `
  insert x xs = if MEM x xs then xs else x::xs`;

val delete_def = Define `
  delete x xs = FILTER (\y. x <> y) xs`;

(* proofs about helper functions *)
val insert_works = store_thm("insert_works", ``
! x list . MEM x (insert x list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
Cases_on `x = h` THEN1 FULL_SIMP_TAC bool_ss [MEM] THEN
FULL_SIMP_TAC bool_ss [] THEN
METIS_TAC [MEM])

(* X is not a member of a list which has all things equal to it filtered out *)
val member_of_filtered_list = store_thm("member_of_filtered_list",
``
    ! x list . ~(MEM x (FILTER (\ y . x <> y) list))
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [FILTER] THEN
Cases_on `x = h` THEN1 METIS_TAC [] THEN
FULL_SIMP_TAC bool_ss [MEM] THEN
METIS_TAC [])

val delete_works = store_thm("delete_works",
``
! x list . ~(MEM x (delete x list))
``, FULL_SIMP_TAC bool_ss [delete_def, member_of_filtered_list])

val mem_insert = store_thm("mem_insert", ``
! x y list .
    MEM x (insert y list) /\ x <> y ==> MEM x list
``,
REPEAT STRIP_TAC THEN
Cases_on `MEM y list` THEN1 FULL_SIMP_TAC bool_ss [insert_def] THEN
METIS_TAC [insert_def, MEM])

val insert_mapping = prove(
  ``(MAP s (insert x list) = MAP t (insert x list)) ==>
  (MAP s list = MAP t list)``,
  RW_TAC bool_ss [insert_def, MAP])

val map_identity = store_thm("map_identity",
  ``!list . MAP (\x.x) list = list``,
    Induct_on `list` THEN1 EVAL_TAC THEN RW_TAC bool_ss [MAP])



(* annotate code with live ranges *)

val get_live_def = Define `
  (get_live [] live = live) /\
  (get_live ((Inst w r1 r2)::code) live =
     insert r1 (insert r2 (delete w (get_live code live))))`;

val get_live_instr_def = Define `
  (get_live_instr [] live = live) /\
  (get_live_instr ((Instr (Op f) w r1 r2)::code) live =
    insert r1 (insert r2 (delete w (get_live_instr code live)))) /\
  (get_live_instr ((Instr (Move) w r1 r2)::code) live =
    insert r1 (delete w (get_live_instr code live)))`;


(* test *)

val test = EVAL ``get_live [Inst 1 2 3; Inst 0 1 2] [0]``


val MEM_insert = prove(
  ``MEM x (insert y ys) = MEM x (y::ys)``,
  SRW_TAC [] [insert_def] THEN METIS_TAC []);

val MEM_inserted_item = prove(``MEM x (insert x xs)``, SIMP_TAC std_ss [MEM_insert, MEM]);

val MEM_after_insertion = store_thm("mem_after_insertion",
``MEM x xs ==> MEM x (insert y xs)``, SRW_TAC [] [insert_def]);

val not_mem_after_insertion = store_thm("not_mem_after_insertion",
``
! a x xs .
~(MEM a (insert x xs)) ==> ~(MEM a xs)
``,
REPEAT STRIP_TAC THEN
Cases_on `x = a` THEN1 FULL_SIMP_TAC bool_ss [MEM, insert_def] THEN
FULL_SIMP_TAC bool_ss [MEM, insert_def] THEN
Cases_on `MEM x xs` THEN METIS_TAC [MEM])


val eval_get_live = store_thm("eval_get_live",
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

val duplicate_free_if_none_equal = store_thm("duplicate_free_if_none_equal",
``
! list . (! x y . x < LENGTH list /\ y < LENGTH list /\ x <> y
  ==> (EL x list <> EL y list))
==> duplicate_free list
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
cheat)  (* TODO *)

val list_length_step = prove(``
    ! n x xs . SUC n < LENGTH (x::xs)
    ==> n < LENGTH xs
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC arith_ss [LENGTH])

val duplicate_free_means_none_equal = store_thm(
    "duplicate_free_means_none_equal",
``
! list x y . duplicate_free list /\ x < LENGTH list /\ y < LENGTH list
  /\ x <> y
==>
EL x list <> EL y list
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `x = 0` THEN1 (
	 FULL_SIMP_TAC bool_ss [EL, HD] THEN
	 FULL_SIMP_TAC bool_ss [duplicate_free_def] THEN
	 Cases_on `y` THEN1 METIS_TAC [] THEN
	 FULL_SIMP_TAC bool_ss [EL, TL] THEN
	 `n < LENGTH list` by METIS_TAC [list_length_step] THEN
	 `MEM (EL n list) list` by METIS_TAC [EL_MEM]) THEN
Cases_on `y = 0` THEN1 (
	 FULL_SIMP_TAC bool_ss [EL, HD] THEN
	 FULL_SIMP_TAC bool_ss [duplicate_free_def] THEN
	 Cases_on `x` THEN1 METIS_TAC [] THEN
	 FULL_SIMP_TAC bool_ss [EL, TL] THEN
	 `n < LENGTH list` by METIS_TAC [list_length_step] THEN
	 `MEM h list` by METIS_TAC [EL_MEM]) THEN
Cases_on `x` THEN1 METIS_TAC [] THEN
Cases_on `y` THEN1 METIS_TAC [] THEN
FULL_SIMP_TAC bool_ss [EL, TL] THEN
`n' < LENGTH list` by METIS_TAC [list_length_step] THEN
`n < LENGTH list` by METIS_TAC [list_length_step] THEN
METIS_TAC [duplicate_free_def])

val duplicate_free_insertion = store_thm("duplicate_free_insertion",``
    !n . duplicate_free (insert n list) = duplicate_free list``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [insert_def] THEN
Cases_on `MEM n list` THEN
FULL_SIMP_TAC bool_ss [duplicate_free_def])

val duplicate_free_deletion = store_thm("duplicate_free_deletion",``
    !n . duplicate_free (delete n list) = duplicate_free list``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
RW_TAC bool_ss [delete_def] THEN
Cases_on `n <> h` THEN1 (
FULL_SIMP_TAC bool_ss [FILTER] THEN
FULL_SIMP_TAC bool_ss [duplicate_free_def] THEN
`duplicate_free (FILTER (\y . n <> y) list) = duplicate_free list`
		by METIS_TAC [delete_def] THEN
`MEM h (FILTER (\y . n <> y) list) = (n <> h) /\ MEM h list`
     by FULL_SIMP_TAC std_ss [MEM_FILTER] THEN
`~(MEM h (FILTER (\y . n <> y) list)) = ~(MEM h list)`
       by METIS_TAC [delete_def] THEN
METIS_TAC []) THEN
FULL_SIMP_TAC bool_ss [FILTER, duplicate_free_def] THEN
cheat) (*todo*)

val get_live_has_no_duplicates = store_thm("get_live_has_no_duplicates",``
!code live . duplicate_free live ==> duplicate_free (get_live code live)``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC)
THEN REPEAT STRIP_TAC
THEN Cases_on `h`
THEN RW_TAC bool_ss [get_live_def]
THEN RW_TAC bool_ss [duplicate_free_insertion, duplicate_free_deletion])


val conflicting_sets_def = Define `
    (conflicting_sets [] live = [live]) /\
    (conflicting_sets ((Inst w r1 r2)::code) live =
        (get_live ((Inst w r1 r2)::code) live)::(conflicting_sets code live))
`

val colouring_respects_conflicting_sets_def = Define `
    (colouring_respects_conflicting_sets (c:num->num) [] = T) /\
    (colouring_respects_conflicting_sets c (s::ss) =
        duplicate_free (MAP c s) /\ colouring_respects_conflicting_sets c ss)
`

val colouring_respects_conflicting_sets_every = store_thm(
    "colouring_respects_conflicting_sets_every",
``
! c sets .
colouring_respects_conflicting_sets c sets
= EVERY (\ list . duplicate_free (MAP c list)) sets
``,
Induct_on `sets` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
METIS_TAC [])

val colouring_ok_alt_def = Define `
    (colouring_ok_alt c code live =
        colouring_respects_conflicting_sets c (conflicting_sets code live))
`

val colouring_ok_def = Define `
    (colouring_ok c [] live = duplicate_free (MAP c live)) /\
    (colouring_ok c ((Inst w r1 r2)::code) live =
    		  duplicate_free (MAP c (get_live ((Inst w r1 r2)::code) live))
    		  /\ colouring_ok c code live)
`

val colouring_ok_def_equivalence = store_thm("colouring_ok_def_equivalence",
    ``colouring_ok_alt c code live = colouring_ok c code live``,
    Induct_on `code`
    THEN1 EVAL_TAC
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC std_ss [colouring_ok_alt_def, colouring_ok_def,
	      conflicting_sets_def, colouring_respects_conflicting_sets_def])


(* compute the union of two sets represented as lists *)
val list_union_def = Define `
    (list_union [] ys = ys) /\
    (list_union (x::xs) ys = insert x (list_union xs ys))
`

val list_union_completeness = store_thm("list_union_completeness",
``
! x list list' .
MEM x list \/ MEM x list' ==> MEM x (list_union list list')
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `x = h` THEN1 (
	 FULL_SIMP_TAC bool_ss [list_union_def] THEN
	 METIS_TAC [insert_works]) THEN
FULL_SIMP_TAC bool_ss [MEM] THEN
FULL_SIMP_TAC bool_ss [list_union_def] THEN
`MEM x (list_union list list')` by METIS_TAC [] THEN
METIS_TAC [insert_def, MEM])

val list_union_flatten_def = Define `
    (list_union_flatten [] = []) /\
    (list_union_flatten (l::ls) = list_union l (list_union_flatten ls))
`

val list_union_flatten_completeness = store_thm(
    "list_union_flatten_completeness",
``
! x list lists .
MEM list lists /\ MEM x list ==> MEM x (list_union_flatten lists)
``,
Induct_on `lists` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [list_union_flatten_def] THEN
Cases_on `h = list` THEN1 METIS_TAC [list_union_completeness] THEN
METIS_TAC [MEM, list_union_completeness])

(* gather list of conflicting registers for a given register *)
val conflicts_for_register_def = Define `
    (conflicts_for_register r code live = delete r
        (list_union_flatten
            (FILTER (\set . MEM r set) (conflicting_sets code live)))
    )
`

(* gather list of registers used by a program *)
val get_registers_def = Define `
    (get_registers [] live = live) /\
    (get_registers ((Inst r0 r1 r2)::code) live =
    		   insert r0 (insert r1 (insert r2 (get_registers code live))))
`

(* get conflicts between registers in the format:
   [(register, [conflicting_register; ...]); ...] *)
val get_conflicts_def = Define `
    (get_conflicts code live =
        MAP (\reg . (reg, conflicts_for_register reg code live))
	(get_registers code live))
`

val test_conflicts = EVAL ``get_conflicts [Inst 1 2 3; Inst 0 1 2] [0]``


(* Proving properties of get_conflicts and related functions *)

(* list_union preserves duplicate freeness *)
val list_union_duplicate_free = store_thm("list_union_duplicate_free",
``
! xs ys . duplicate_free xs /\ duplicate_free ys
  ==> duplicate_free (list_union xs ys)
``,
Induct_on `xs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
`duplicate_free xs` by METIS_TAC [duplicate_free_def] THEN
Cases_on `MEM h (list_union xs ys)` THEN1 (
	 FULL_SIMP_TAC bool_ss [] THEN	 
	 METIS_TAC []) THEN
FULL_SIMP_TAC bool_ss [] THEN
`duplicate_free (list_union xs ys)` by METIS_TAC [] THEN
FULL_SIMP_TAC bool_ss [duplicate_free_def])

(* list_union_flatten preserves duplicate freeness *)
val list_union_flatten_duplicate_free = store_thm(
    "list_union_flatten_duplicate_free",
``
! lists .
EVERY (\list . duplicate_free list) lists
==> duplicate_free (list_union_flatten lists)
``,
Induct_on `lists` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
FULL_SIMP_TAC bool_ss [EVERY_DEF] THEN
`duplicate_free (list_union_flatten lists)` by METIS_TAC [] THEN
METIS_TAC [list_union_duplicate_free])

(* conflicting_sets generates duplicate-free sets *)
val conflicting_sets_duplicate_free = store_thm(
    "conflicting_sets_duplicate_free",
``
! code live . duplicate_free live
  ==> EVERY (\list . duplicate_free list) (conflicting_sets code live)
``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [conflicting_sets_def, get_live_def, EVERY_DEF] THEN
`duplicate_free (get_live code live)`
        by METIS_TAC [get_live_has_no_duplicates] THEN
METIS_TAC [duplicate_free_insertion, duplicate_free_deletion])

(* If 'EVERY P list' holds, then it also holds after the list is filtered *)
val every_filter_implication = store_thm("every_filter_implication",
``
! P Q list .
EVERY P list ==> EVERY P (FILTER Q list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [EVERY_DEF] THEN
Cases_on `Q h` THEN1 (EVAL_TAC THEN FULL_SIMP_TAC bool_ss [EVERY_DEF]) THEN
EVAL_TAC THEN FULL_SIMP_TAC bool_ss [EVERY_DEF])

(* The list of conflicts for a register is duplicate_free *)
val conflicts_for_register_duplicate_free = store_thm(
    "conflicts_for_register_duplicate_free",
``
! code live r . (duplicate_free live)
  ==> duplicate_free (conflicts_for_register r code live)
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [conflicts_for_register_def] THEN
`EVERY (\list . duplicate_free list)
       (FILTER (\set . MEM r set) (conflicting_sets code live))`
       by ALL_TAC THEN1(
       `EVERY (\list . duplicate_free list) (conflicting_sets code live)`
	      by ALL_TAC
        THEN1 (METIS_TAC [conflicting_sets_duplicate_free]) THEN
	METIS_TAC [every_filter_implication]) THEN
METIS_TAC [list_union_flatten_duplicate_free, duplicate_free_deletion])

(* The list of all registers is duplicate_free *)
val get_registers_duplicate_free = store_thm("get_registers_duplicate_free",
``
! code live . (duplicate_free live)
  ==> duplicate_free (get_registers code live)
``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
`duplicate_free (get_registers code live)` by METIS_TAC [] THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [get_registers_def] THEN
METIS_TAC [duplicate_free_insertion])

(* A register does not feature in the list of registers conflicting with it *)
val register_does_not_conflict_with_self = store_thm(
    "register_does_not_conflict_with_self",
``
    ! r code live .
    ~(MEM r (conflicts_for_register r code live))
``,
FULL_SIMP_TAC std_ss [conflicts_for_register_def] THEN
EVAL_TAC THEN
METIS_TAC [member_of_filtered_list])

(* Registers not used in the program do not feature in any instruction *)
val unused_registers_are_not_used = store_thm("unused_registers_are_not_used",
``
! r code live w r1 r2 .
~(MEM r (get_registers code live)) /\ (MEM (Inst w r1 r2) code)
==> (r <> w) /\ (r <> r1) /\ (r <> r2)
``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
(Cases_on `h = (Inst w r1 r2)` THEN1 (
	 FULL_SIMP_TAC bool_ss [get_registers_def] THEN
	 METIS_TAC [insert_works, not_mem_after_insertion]) THEN
FULL_SIMP_TAC bool_ss [MEM] THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [get_registers_def] THEN
METIS_TAC [not_mem_after_insertion]))

(* Registers not used in the program do not feature in get_live *)
val unused_registers_not_in_get_live = store_thm(
    "unused_registers_not_in_get_live",
``
! r code live .
~(MEM r (get_registers code live))
==> ~(MEM r (get_live code live))
``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
`(r <> n) /\ (r <> n0) /\ (r <> n1)`
    by METIS_TAC [unused_registers_are_not_used, MEM] THEN
FULL_SIMP_TAC bool_ss [get_registers_def] THEN
`~(MEM r (get_live code live))` by METIS_TAC [not_mem_after_insertion] THEN
FULL_SIMP_TAC bool_ss [get_live_def] THEN
`MEM r (delete n (get_live code live))` by METIS_TAC [mem_insert] THEN
METIS_TAC [delete_def, MEM_FILTER])

(* Registers not used in the program do not feature in any conflicting set *)
val unused_registers_not_in_conflicting_sets = store_thm(
    "unused_registers_not_in_conflicting_sets",
``
! r code live set .
~(MEM r (get_registers code live)) /\ (MEM set (conflicting_sets code live))
==>
~(MEM r set)
``,
Induct_on `code` THEN1 (EVAL_TAC THEN METIS_TAC []) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
`(r <> n) /\ (r <> n0) /\ (r <> n1)`
    by METIS_TAC [unused_registers_are_not_used, MEM] THEN
FULL_SIMP_TAC bool_ss [conflicting_sets_def, get_registers_def] THEN
`~(MEM r (get_registers code live))` by METIS_TAC [not_mem_after_insertion] THEN
Tactical.REVERSE (Cases_on `set' = get_live (Inst n n0 n1::code) live`)
	THEN1 METIS_TAC [MEM] THEN
FULL_SIMP_TAC bool_ss [get_live_def] THEN
`~(MEM r (get_live code live))`
       by METIS_TAC [unused_registers_not_in_get_live] THEN
`MEM r (delete n (get_live code live))` by METIS_TAC [mem_insert] THEN
METIS_TAC [delete_def, MEM_FILTER])

(* Regisers not used in the program do not conflict with anything *)
val unused_registers_do_not_conflict = store_thm(
    "unused_registers_do_not_conflict",
``
! r code live .
~(MEM r (get_registers code live)) ==>
((conflicts_for_register r code live) = [])
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [conflicts_for_register_def, conflicting_sets_def] THEN
`! set . MEM set (conflicting_sets code live) ==> ~(MEM r set)`
   by METIS_TAC [unused_registers_not_in_conflicting_sets] THEN
`EVERY (\set . ~(MEM r set)) (conflicting_sets code live)`
       by FULL_SIMP_TAC bool_ss [EVERY_MEM] THEN
`(FILTER (\set . MEM r set) (conflicting_sets code live)) = []`
	 by METIS_TAC [FILTER_EQ_NIL] THEN
FULL_SIMP_TAC bool_ss [] THEN
EVAL_TAC)



(* Proofs linking conflicting_sets and conflicts_for_register, to be used for
proving that a 'satisfactory' colouring will satisfy colouring_ok *)

(* If a list of lists is being filtered for whether they contain x, and x is
in 'list', 'list' is in the result. *)
val filter_by_membership = store_thm("filter_by_membership",
``
! list lists x .
MEM list lists /\ MEM x list ==> MEM list (FILTER (\list . MEM x list) lists)
``,
Induct_on `lists` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
Cases_on `list = h` THEN1 (
	 FULL_SIMP_TAC bool_ss [] THEN
	 METIS_TAC [MEM]) THEN
FULL_SIMP_TAC std_ss [MEM] THEN
Cases_on `MEM x h` THEN
FULL_SIMP_TAC bool_ss [] THEN
METIS_TAC [MEM])

(* Shows that registers in the same conflicting set will appear in each other's
conflicts_for_register list *)
val conflicting_registers_appear_in_each_others_conflicts = store_thm(
    "conflicting_registers_appear_in_each_others_conflicts",
``
! c code live r s .
MEM c (conflicting_sets code live) /\ MEM r c /\ MEM s c /\ r <> s
==>
MEM r (conflicts_for_register s code live)
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [conflicts_for_register_def] THEN
`MEM c (FILTER (\set . MEM s set) (conflicting_sets code live))`
     by METIS_TAC [filter_by_membership] THEN
FULL_SIMP_TAC std_ss [delete_def] THEN
`MEM r (list_union_flatten
     (FILTER (\set . MEM s set) (conflicting_sets code live)))`
     by METIS_TAC [list_union_flatten_completeness] THEN
FULL_SIMP_TAC bool_ss [MEM_FILTER])

(* Any colouring respecting conflicts_for_register will also respect the set
of conflicting sets *)
val respecting_register_conflicts_respects_conflicting_sets = store_thm(
    "respecting_register_conflicts_respects_conflicting_sets",
``
! col code live .
duplicate_free live ==>
(! r . ~(MEM (col r) (MAP col (conflicts_for_register r code live))))
==>
EVERY (\s . duplicate_free (MAP col s)) (conflicting_sets code live)
``,
FULL_SIMP_TAC bool_ss [EVERY_MEM] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE(`
! x y . x < LENGTH (MAP col s) /\ y < LENGTH (MAP col s) /\ x <> y
==> EL x (MAP col s) <> EL y (MAP col s)` by ALL_TAC)
    THEN1 METIS_TAC [duplicate_free_if_none_equal] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [LENGTH_MAP] THEN
`col (EL x s) = col (EL y s)` by METIS_TAC [EL_MAP] THEN
`duplicate_free s`
		by METIS_TAC [conflicting_sets_duplicate_free, EVERY_MEM] THEN
`EL x s <> EL y s` by METIS_TAC [duplicate_free_means_none_equal] THEN
`MEM (EL x s) s` by METIS_TAC [MEM_EL] THEN
`MEM (EL y s) s` by METIS_TAC [MEM_EL] THEN
`MEM (EL x s) (conflicts_for_register (EL y s) code live)`
     by METIS_TAC [conflicting_registers_appear_in_each_others_conflicts] THEN
`MEM (col (EL x s)) (MAP col (conflicts_for_register (EL y s) code live))`
     by METIS_TAC [MEM_MAP] THEN
`~(MEM (col (EL y s)) (MAP col (conflicts_for_register (EL y s) code live)))`
       by METIS_TAC [] THEN
`col (EL x s) <> col (EL y s)` by METIS_TAC [])



val mem_after_map = prove(``! x xs (c:num->num) .
    MEM x xs ==> MEM (c x) (MAP c xs)``,
RW_TAC std_ss [MEM_MAP] THEN Q.EXISTS_TAC `x`
THEN EVAL_TAC THEN FULL_SIMP_TAC bool_ss [])

(* proving a simplified version of the injectivity goal, for the case where
'code' is empty *)
val colouring_ok_injectivity_base = store_thm("colouring_ok_injectivity_base",
``!(c:num->num) live x y .
	colouring_ok c [] live /\ MEM x live /\ MEM y live /\ (c x = c y)
	==> (x = y)
``,
FULL_SIMP_TAC std_ss [colouring_ok_def]
THEN Induct_on `live`
THEN1 (EVAL_TAC THEN DECIDE_TAC)
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [MAP, duplicate_free_def]
THEN Cases_on `x = y`
(* t *)
THEN1 DECIDE_TAC
(* f *)
THEN Cases_on `x = h`
	 (* t *)
	 THEN1(`MEM y live` by METIS_TAC [MEM]
	 THEN IMP_RES_TAC mem_after_map
	 THEN `MEM (c y) (MAP c live)` by METIS_TAC []
	 THEN `~(MEM (c x) (MAP c live))` by METIS_TAC []
	 THEN EVAL_TAC
	 THEN METIS_TAC [])
	 (* f *)
	 THEN Cases_on `y = h`
	      (* t *)
	      THEN1(`MEM x live` by METIS_TAC [MEM]
	      THEN IMP_RES_TAC mem_after_map
	      THEN `MEM (c x) (MAP c live)` by METIS_TAC []
	      THEN `~(MEM (c x) (MAP c live))` by METIS_TAC [])
	      (* f *)
	      THEN `MEM x live /\ MEM y live` by METIS_TAC [MEM]
	      THEN `x = y` by METIS_TAC []
)



val no_dead_code_def = Define `
    (no_dead_code [] _ = T) /\
    (no_dead_code ((Inst w r1 r2)::code) live = MEM w (get_live code live)
    		  /\ no_dead_code code live)
`

val remove_dead_code_def = Define `
    (remove_dead_code [] live = []) /\
    (remove_dead_code ((Inst w r1 r2)::code) live =
            let (newcode = remove_dead_code code live) in
    		      if (MEM w (get_live newcode live))
		      	 then (Inst w r1 r2)::newcode
			 else newcode)
`

val remove_dead_code_works = store_thm("remove_dead_code_works",
``
! code live . no_dead_code (remove_dead_code code live) live
``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
Cases_on `h` THEN
FULL_SIMP_TAC std_ss [remove_dead_code_def, LET_DEF] THEN
REPEAT STRIP_TAC THEN
Q.ASM_CASES_TAC `MEM n (get_live (remove_dead_code code live) live)` THEN
FULL_SIMP_TAC bool_ss [no_dead_code_def])


(* no_dead_code is preserved by removing the first instruction *)
val no_dead_code_preserved = store_thm("no_dead_code_preserved",
``
    no_dead_code (Inst n n0 n1 :: code) live ==>
    no_dead_code code live``,
    RW_TAC std_ss [no_dead_code_def])

(* colouring_ok is preserved by removing the first instruction *)
val colouring_ok_preserved = store_thm("colouring_ok_preserved",
``
    colouring_ok c (Inst n n0 n1 :: code) live ==>
    colouring_ok c code live``,
    RW_TAC std_ss [colouring_ok_def]);

val duplicate_free_MAP_IMP_NEQ = store_thm("duplicate_free_MAP_IMP_NEQ",
  ``!c live x y.
      duplicate_free (MAP c live) /\ x <> y /\ MEM x live /\ MEM y live ==>
      c x <> c y``,
  Induct_on `live`
  THEN1 (EVAL_TAC THEN DECIDE_TAC)
  THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [MAP, duplicate_free_def]
  THEN Cases_on `x = h` THEN1 (METIS_TAC [MEM, MAP, MEM_MAP])
  THEN Cases_on `y = h` THEN1 (METIS_TAC [MEM, MAP, MEM_MAP])
  THEN METIS_TAC [MEM]);

val colouring_ok_IMP = store_thm("colouring_ok_IMP",
  ``colouring_ok c code live ==>
    duplicate_free (MAP c (get_live code live))``,
  Cases_on `code` THEN TRY (Cases_on `h`)
  THEN EVAL_TAC
  THEN RW_TAC std_ss [colouring_ok_def]);

val colouring_ok_injective = store_thm("colouring_ok_injective",
``
    ! c code live x y .
      (no_dead_code code live) /\
      (colouring_ok c code live) /\ ~(x = y) /\
      (MEM x (get_live code live)) /\ (MEM y (get_live code live))
    ==> ~(c x = c y) ``,
  REPEAT STRIP_TAC
  THEN IMP_RES_TAC colouring_ok_IMP
  THEN IMP_RES_TAC duplicate_free_MAP_IMP_NEQ)

val colouring_ok_IMP_eval_apply = store_thm("colouring_ok_IMP_eval_apply",
``
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
  THEN Tactical.REVERSE (`(c n = c e) = (n = e)` by ALL_TAC)
  THEN1 FULL_SIMP_TAC std_ss []
  THEN Cases_on `n = e` THEN FULL_SIMP_TAC std_ss []
  THEN FULL_SIMP_TAC std_ss [no_dead_code_def, colouring_ok_def]
  THEN IMP_RES_TAC colouring_ok_injective)


(* Functions for computing a preference graph for a block of code *)
(* Add a pair of registers to each other's preferences *)
val add_preference_pair_def = Define `
    (add_preference_pair (x:num, y:num) prefs =
        let xs = (prefs x) in
	let ys = (prefs y) in
	    (x =+ (y::xs)) ((y =+ (x::ys)) prefs))
`

(* Compute the preference graph for a block of code *)
val compute_preferences_def = Define `
    (compute_preferences [] = \x.[]) /\
    (compute_preferences ((Instr Move dest source _)::code) =
        add_preference_pair (source, dest) (compute_preferences code)) /\
    (compute_preferences (_::code) = compute_preferences code)
`

(* Function to remove identity moves after register allocation *)
val remove_identity_moves_def = Define `
    (remove_identity_moves [] = []) /\
    (remove_identity_moves ((Instr Move d s v)::code) =
        if (d = s) then (remove_identity_moves code)
	else ((Instr Move d s v)::(remove_identity_moves code))) /\
    (remove_identity_moves (instr::code) = instr::(remove_identity_moves code))
`

val remove_identity_moves_correct = store_thm("remove_identity_moves_correct",
``
! s code live .
eval_instr s code = eval_instr s (remove_identity_moves code)
``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
Cases_on `o'` THEN1 (EVAL_TAC THEN METIS_TAC []) THEN
EVAL_TAC THEN
Cases_on `n = n0` THEN1 FULL_SIMP_TAC bool_ss [APPLY_UPDATE_ID] THEN
FULL_SIMP_TAC bool_ss [] THEN
EVAL_TAC)


(* Register spilling
The approach used is to check where a register is greater than or equal to K,
the number of available registers, and if it is to generate a load or store
as appropriate. If it is an output register, generate a store, and if it is an
input register, generate a load. Three temporary registers are allocated at
K, K+1 and K+2 for output and two inputs; these should be used for instructions
where an input or output has been spilled.
*)

(* Output code type with load and store instructions *)
val _ = Hol_datatype `
    spill_inst = Load of num=>num | Store of num=>num
    | ThreeAddr of num=>num=>num`

val merge_def = Define `
    (merge (r, s) K = (\x . if x >= K then s x else r x))
`

val split_def = Define `
    (split r K =
    ((\x . if x < K then r x else 0), (\x . if x >= K then r x else 0)))
`

val eval_stack_def = Define `
    (eval_stack f r s K [] = merge (r, s) K) /\
    (eval_stack f r s K ((Load reg mem)::code) =
    		eval_stack f ((reg =+ s mem) r) s K code) /\
    (eval_stack f r s K ((Store mem reg)::code) =
    		eval_stack f r ((mem =+ r reg) s) K code) /\
    (eval_stack f r s K ((ThreeAddr w r1 r2)::code) =
    		eval_stack f ((w =+ f (r r1) (r r2)) r) s K code)
`

(* Make sure the result of an instruction goes to a temporary variable which is
then stored in memory *)
val spill_stores_def = Define `
    (spill_stores K [] = []) /\
    (spill_stores K ((ThreeAddr w r1 r2)::code) =
    if w >= K then (ThreeAddr K r1 r2)::(Store w K)::(spill_stores K code)
    else (ThreeAddr w r1 r2)::(spill_stores K code)) /\
    (spill_stores K ((Load d s)::code) = (Load d s)::(spill_stores K code)) /\
    (spill_stores K ((Store d s)::code) = (Store d s)::(spill_stores K code))`

(* Ensure registers which are spilled to memory are loaded to temporaries
before use *)
val spill_loads_def = Define `
    (spill_loads K [] = []) /\
    (spill_loads K ((Inst w r1 r2)::code) =
    if (r1 >= K /\ r2 >= K) then
       (Load (K+1) r1)::(Load (K+2) r2)::(ThreeAddr w (K+1) (K+2))
       	     ::(spill_loads K code)
    else if (r1 >= K) then
       (Load (K+1) r1)::(ThreeAddr w (K+1) r2)::(spill_loads K code)
    else if (r2 >= K) then
       (Load (K+2) r2)::(ThreeAddr w r1 (K+2))::(spill_loads K code)
    else (ThreeAddr w r1 r2)::(spill_loads K code))
`

val spill_loads_stores_def = Define `
    (spill_loads_stores K code = spill_stores K (spill_loads K code))
`

val merge_split_identity = prove(``
! s K . merge (split s K) K = s
``,
EVAL_TAC THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC arith_ss [] THEN
METIS_TAC [])

val split_store_equality = prove(``
! s (x:num) (K:num) .
s = (\x . if (x >= K) then (s x) else if (x < K) then (s x) else 0)
``,
REPEAT STRIP_TAC THEN
Tactical.REVERSE (
`!x . s x = (\x . if (x >= K') then (s x) else if (x < K') then (s x) else 0) x`
	by ALL_TAC) THEN1 IMP_RES_TAC EQ_EXT THEN
REPEAT STRIP_TAC THEN
Cases_on `x >= K'` THEN1 (EVAL_TAC THEN FULL_SIMP_TAC bool_ss []) THEN
EVAL_TAC THEN FULL_SIMP_TAC arith_ss [])

val split_correctness = prove(``
! s K r m .
(split s K = (r, m)) ==>
(! x . x >= K ==> (m x = s x)) /\
(! x . x < K ==> (r x = s x))
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [split_def] THEN
METIS_TAC [])

(*``
! f code s1 s2 K r m .
((split s1 K) = (r, m)) ==>
(eval f s1 code = eval_stack f r m K (spill_loads_stores K code))
``
Induct_on `code` THEN1 (
	  EVAL_TAC THEN FULL_SIMP_TAC bool_ss []
	  	   THEN METIS_TAC [split_store_equality]) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
EVAL_TAC THEN
Cases_on `n0 >= K'` THEN1 (
	 FULL_SIMP_TAC bool_ss [] THEN
	 Cases_on `n1 >= K'` THEN1 (
	 	  FULL_SIMP_TAC bool_ss [] THEN
		  EVAL_TAC THEN
		  Cases_on `n >= K'` THEN1 (
		  	   FULL_SIMP_TAC bool_ss [] THEN
			   EVAL_TAC THEN
			   FULL_SIMP_TAC arith_ss [] THEN
			   cheat
		  ) THEN
		  FULL_SIMP_TAC arith_ss [] THEN
		  EVAL_TAC THEN
		  FULL_SIMP_TAC arith_ss []
	 )
)*)
	   


val _ = export_theory();
