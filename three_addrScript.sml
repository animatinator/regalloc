open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory rich_listTheory
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
val insert_works = prove(``
! x list . MEM x (insert x list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
Cases_on `x = h` THEN1 FULL_SIMP_TAC bool_ss [MEM] THEN
FULL_SIMP_TAC bool_ss [] THEN
METIS_TAC [MEM])

val mem_insert = prove(``
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


(* test *)

val test = EVAL ``get_live [Inst 1 2 3; Inst 0 1 2] [0]``

(* only live variables matter *)

val MEM_insert = prove(
  ``MEM x (insert y ys) = MEM x (y::ys)``,
  SRW_TAC [] [insert_def] THEN METIS_TAC []);

val MEM_inserted_item = prove(``MEM x (insert x xs)``, SIMP_TAC std_ss [MEM_insert, MEM]);

val MEM_after_insertion = prove(``MEM x xs ==> MEM x (insert y xs)``, SRW_TAC [] [insert_def]);

val not_mem_after_insertion = prove(``
! a x xs .
~(MEM a (insert x xs)) ==> ~(MEM a xs)
``,
REPEAT STRIP_TAC THEN
Cases_on `x = a` THEN1 FULL_SIMP_TAC bool_ss [MEM, insert_def] THEN
FULL_SIMP_TAC bool_ss [MEM, insert_def] THEN
Cases_on `MEM x xs` THEN METIS_TAC [MEM])


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

val duplicate_free_if_none_equal = prove(``
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

val duplicate_free_means_none_equal = prove(``
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

val colouring_respects_conflicting_sets_every = prove(``
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

val colouring_ok_def_equivalence = prove(
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

val list_union_completeness = prove(``
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

val list_union_flatten_completeness = prove(``
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
val list_union_duplicate_free = prove(``
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
val list_union_flatten_duplicate_free = prove(``
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
val conflicting_sets_duplicate_free = prove(``
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
val every_filter_implication = prove(``
! P Q list .
EVERY P list ==> EVERY P (FILTER Q list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [EVERY_DEF] THEN
Cases_on `Q h` THEN1 (EVAL_TAC THEN FULL_SIMP_TAC bool_ss [EVERY_DEF]) THEN
EVAL_TAC THEN FULL_SIMP_TAC bool_ss [EVERY_DEF])

(* The list of conflicts for a register is duplicate_free *)
val conflicts_for_register_duplicate_free = prove(``
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
val get_registers_duplicate_free = prove(``
! code live . (duplicate_free live)
  ==> duplicate_free (get_registers code live)
``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
`duplicate_free (get_registers code live)` by METIS_TAC [] THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [get_registers_def] THEN
METIS_TAC [duplicate_free_insertion])

(* X is not a member of a list which has all things equal to it filtered out *)
val member_of_filtered_list = prove(``
    ! x list . ~(MEM x (FILTER (\ y . x <> y) list))
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [FILTER] THEN
Cases_on `x = h` THEN1 METIS_TAC [] THEN
FULL_SIMP_TAC bool_ss [MEM] THEN
METIS_TAC [])

(* A register does not feature in the list of registers conflicting with it *)
val register_does_not_conflict_with_self = prove(``
    ! r code live .
    ~(MEM r (conflicts_for_register r code live))
``,
FULL_SIMP_TAC std_ss [conflicts_for_register_def] THEN
EVAL_TAC THEN
METIS_TAC [member_of_filtered_list])

(* Registers not used in the program do not feature in any instruction *)
val unused_registers_are_not_used = prove(``
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
val unused_registers_not_in_get_live = prove(``
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
val unused_registers_not_in_conflicting_sets = prove(``
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
REVERSE (Cases_on `set' = get_live (Inst n n0 n1::code) live`)
	THEN1 METIS_TAC [MEM] THEN
FULL_SIMP_TAC bool_ss [get_live_def] THEN
`~(MEM r (get_live code live))`
       by METIS_TAC [unused_registers_not_in_get_live] THEN
`MEM r (delete n (get_live code live))` by METIS_TAC [mem_insert] THEN
METIS_TAC [delete_def, MEM_FILTER])

(* Regisers not used in the program do not conflict with anything *)
val unused_registers_do_not_conflict = prove(``
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
val filter_by_membership = prove(``
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
val conflicting_registers_appear_in_each_others_conflicts = prove(``
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
val respecting_register_conflicts_respects_conflicting_sets = prove(``
! col code live .
duplicate_free live ==>
(! r . ~(MEM (col r) (MAP col (conflicts_for_register r code live))))
==>
EVERY (\s . duplicate_free (MAP col s)) (conflicting_sets code live)
``,
FULL_SIMP_TAC bool_ss [EVERY_MEM] THEN
REPEAT STRIP_TAC THEN
REVERSE(`
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
val colouring_ok_injectivity_base = prove(``!(c:num->num) live x y .
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

val remove_dead_code_works = prove(``
! code live . no_dead_code (remove_dead_code code live) live
``,
Induct_on `code` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
Cases_on `h` THEN
FULL_SIMP_TAC std_ss [remove_dead_code_def, LET_DEF] THEN
REPEAT STRIP_TAC THEN
Q.ASM_CASES_TAC `MEM n (get_live (remove_dead_code code live) live)` THEN
FULL_SIMP_TAC bool_ss [no_dead_code_def])


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

val duplicate_free_MAP_IMP_NEQ = prove(
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

val colouring_ok_IMP = prove(
  ``colouring_ok c code live ==>
    duplicate_free (MAP c (get_live code live))``,
  Cases_on `code` THEN TRY (Cases_on `h`)
  THEN EVAL_TAC
  THEN RW_TAC std_ss [colouring_ok_def]);

val colouring_ok_injective = prove(``
    ! c code live x y .
      (no_dead_code code live) /\
      (colouring_ok c code live) /\ ~(x = y) /\
      (MEM x (get_live code live)) /\ (MEM y (get_live code live))
    ==> ~(c x = c y) ``,
  REPEAT STRIP_TAC
  THEN IMP_RES_TAC colouring_ok_IMP
  THEN IMP_RES_TAC duplicate_free_MAP_IMP_NEQ)

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


(*
(* Spilling function for when there are only 'k' physical registers available -
spill registers outside of the bound by placing them in the N+ range *)
val spill_high_registers_def = Define `
    (spill_high_registers c k N =
    			  (\r . if ((c r) >= k) then ((c r) + N) else (c r)))
`


val duplicate_free_after_spilling = prove(``
! c k N list .
duplicate_free (MAP c list) /\ k < N
==>
duplicate_free (MAP (spill_high_registers c k N) list)
``,
REPEAT STRIP_TAC THEN

`! x y . x < LENGTH (MAP c list) /\ y < LENGTH (MAP c list) /\ x <> y
==> EL x (MAP c list) <> EL y (MAP c list)`
    by METIS_TAC [duplicate_free_means_none_equal] THEN

`LENGTH (MAP (\r . if c r >= k then c r + 1000 else c r) list)
	= LENGTH (MAP c list)` by METIS_TAC [LENGTH_MAP] THEN
REVERSE (`! x y . x < LENGTH (MAP c list) /\ y < LENGTH (MAP c list) /\ x <> y
==> EL x (MAP (\r . if c r >= k then c r + 1000 else c r) list)
<> EL y (MAP (\r . if c r >= k then c r + 1000 else c r) list)` by ALL_TAC)
   THEN1 METIS_TAC [duplicate_free_if_none_equal] THEN
REPEAT STRIP_TAC THEN

`EL x (MAP c list) <> EL y (MAP c list)` by METIS_TAC [] THEN
(* TODO: Can this be used to show the elements aren't equal when the map is the
one with the branch? *)
cheat)


val colouring_ok_after_spilling = prove(``
! c k code live .
colouring_ok_alt c code live
==>
colouring_ok_alt (spill_high_registers c k) code live
``,
Induct_on `code` THEN1
	  (EVAL_TAC THEN METIS_TAC [duplicate_free_after_spilling]) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [colouring_ok_alt_def,
        colouring_respects_conflicting_sets_def, conflicting_sets_def] THEN
FULL_SIMP_TAC bool_ss [spill_high_registers_def] THEN
METIS_TAC [duplicate_free_after_spilling])
*)


(* Different approach - will define spill_high_registers as a function applied
to the result of the colouring, and show that it maintains duplicate-freeness *)
val spill_def = Define `
    (spill x = x + 1000)
`

val spill_high_registers_def = Define `
    (spill_high_registers k = (\x . if x >= k then (spill x) else x))
`

val injective_def = Define `
    (injective f = !x y . (f x = f y) ==> (x = y))
`

(* Something like this: *)
val injective_preserves_duplicate_freeness = prove(``
! list f .
  (duplicate_free list) /\ (injective f)
  ==> duplicate_free (MAP f list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
FULL_SIMP_TAC std_ss [duplicate_free_def] THEN
FULL_SIMP_TAC std_ss [injective_def] THEN
FULL_SIMP_TAC std_ss [MEM_MAP] THEN
STRIP_TAC THEN
Cases_on `h = y` THEN1 METIS_TAC [] THEN
METIS_TAC [])

(* Then show that applying it to only some elements still yields
duplicate-freeness *)


val _ = export_theory();
