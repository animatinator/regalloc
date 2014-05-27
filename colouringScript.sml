open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory sortingTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory;

open three_addrTheory;

val _ = new_theory "colouring";


(* Get list of vertices from a graph *)
val get_vertices_def = Define `
    (get_vertices [] = []) /\
    (get_vertices ((v, vs)::es) = v::(get_vertices es))
`

(* Graph contains a vertex *)
val has_vertex_def = Define `
    (has_vertex [] (v:num) = F) /\
    (has_vertex ((ver, _)::cs) v = if (v = ver) then T else (has_vertex cs v))
`

(* Graph has no duplicate vertices *)
val graph_duplicate_free_def = Define `
    (graph_duplicate_free [] = T) /\
    (graph_duplicate_free ((r, rs)::cs) =
    (! rs' . ~(MEM (r, rs') cs)) /\ graph_duplicate_free cs)
`

(* Vertex is not linked to itself, and there are no duplicates in its edge
list *)
val edge_list_well_formed_def = Define `
    (edge_list_well_formed ((v:num), (edges:num list)) = ~(MEM v edges)
    			   /\ duplicate_free edges)
`

(* All edge lists in the graph are well-formed *)
val graph_edge_lists_well_formed_def = Define `
    (graph_edge_lists_well_formed es = EVERY (\x . edge_list_well_formed x) es)
`

(* The graph reflects conflicts accurately: any vertex linked to the current one
will also have a link to this vertex; the graph is symmetric *)
val graph_reflects_conflicts_def = Define `
    (graph_reflects_conflicts cs = ! r1 r2 rs1 rs2 .
        MEM (r1, rs1) cs /\ MEM (r2, rs2) cs /\ MEM r1 rs2 ==>
	    MEM r2 rs1)
`

(* Dropping a vertex preserves graph_reflects_conflicts *)
val graph_reflects_conflicts_preserved = store_thm(
    "graph_reflects_conflicts_preserved", ``
! r rs cs .
graph_reflects_conflicts ((r,rs)::cs) ==>
graph_reflects_conflicts cs
``,
EVAL_TAC THEN
REPEAT STRIP_TAC THEN
METIS_TAC [])


(* Proving that graphs generated in three_addrScript have the necessary
properties *)
val generated_edge_lists_well_formed = store_thm(
	"generated_edge_lists_well_formed", ``
! r code live . duplicate_free live ==>
edge_list_well_formed (r, conflicts_for_register r code live)
``,
FULL_SIMP_TAC std_ss [edge_list_well_formed_def] THEN
REPEAT STRIP_TAC THEN1 METIS_TAC [register_does_not_conflict_with_self] THEN
METIS_TAC [conflicts_for_register_duplicate_free])

(* If a function f makes P hold of any input, then P holds over all elements
of the list that is the result of mapping f over a list *)
val every_map = store_thm("every_map", ``
! (P:(num # num list) -> bool) (f:num->(num # num list)) (list:num list) .
(! x . P (f x)) ==> EVERY P (MAP f list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
METIS_TAC [])

(* The graph generated by the clash graph generation code is well-formed *)
val generated_graph_edge_lists_well_formed = store_thm(
	"generated_graph_edge_lists_well_formed", ``
! code live . duplicate_free live ==>
graph_edge_lists_well_formed (get_conflicts code live)
``,
FULL_SIMP_TAC std_ss [graph_edge_lists_well_formed_def] THEN
FULL_SIMP_TAC std_ss [get_conflicts_def] THEN
REPEAT STRIP_TAC THEN
`! reg . (\edge . edge_list_well_formed edge)
   ((\ reg . (reg, conflicts_for_register reg code live)) reg)`
   	 by METIS_TAC [generated_edge_lists_well_formed] THEN
ASSUME_TAC every_map THEN
Q.PAT_ASSUM `! P f list . (! x . P (f x)) ==> EVERY P (MAP f list)`
	    (ASSUME_TAC o Q.SPECL [`(\edge. edge_list_well_formed edge)`,
`(\ reg . (reg, conflicts_for_register reg code live))`,
`(get_registers code live)`]) THEN
METIS_TAC [every_map])

val not_mem_after_graph_map = store_thm("not_mem_after_graph_map",
``
! x list f .
~(MEM x list) ==> ! xs . (~(MEM (x, xs) (MAP (\x . (x, f x)) list)))
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [MEM, MAP] THEN1 METIS_TAC [PAIR_EQ] THEN
METIS_TAC [])

val graph_duplicate_free_if_vertices_duplicate_free = store_thm(
    "graph_duplicate_free_if_vertices_duplicate_free",
``
! list f .
duplicate_free list ==>
graph_duplicate_free (MAP (\x . x, f x) list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
FULL_SIMP_TAC bool_ss [duplicate_free_def] THEN
METIS_TAC [not_mem_after_graph_map])

val generated_graph_duplicate_free = store_thm(
    "generated_graph_duplicate_free", ``
! code live . duplicate_free live ==>
graph_duplicate_free (get_conflicts code live)
``,
FULL_SIMP_TAC std_ss [get_conflicts_def] THEN
REPEAT STRIP_TAC THEN
`duplicate_free (get_registers code live)`
    by METIS_TAC [get_registers_duplicate_free] THEN
METIS_TAC [graph_duplicate_free_if_vertices_duplicate_free])

val generated_graph_reflects_conflicts = store_thm(
    "generated_graph_reflects_conflicts", ``
! code live . duplicate_free live ==>
graph_reflects_conflicts (get_conflicts code live)
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [get_conflicts_def] THEN
FULL_SIMP_TAC std_ss [graph_reflects_conflicts_def] THEN
REPEAT STRIP_TAC THEN
`rs1 = conflicts_for_register r1 code live` by cheat THEN
`rs2 = conflicts_for_register r2 code live` by cheat THEN
FULL_SIMP_TAC bool_ss [] THEN
`r1 <> r2` by METIS_TAC [register_does_not_conflict_with_self] THEN
IMP_RES_TAC conflicts_come_from_shared_conflicting_set THEN
METIS_TAC [conflicting_registers_appear_in_each_others_conflicts])



(* Colouring satisfies constraints *)
val colouring_satisfactory_def = Define `
    (colouring_satisfactory col [] = T) /\
    (colouring_satisfactory col ((r, rs)::cs) = ~(MEM (col r) (MAP col rs))
    			    /\ (colouring_satisfactory col cs))
`


val colouring_satisfactory_on_one_vertex = store_thm(
	"colouring_satisfactory_on_one_vertex", ``
! c cs r rs c .
colouring_satisfactory c cs /\ MEM (r, rs) cs
==> ~(MEM (c r) (MAP c rs))
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h = (r, rs)` 
	 THEN1 FULL_SIMP_TAC bool_ss [colouring_satisfactory_def] THEN
FULL_SIMP_TAC bool_ss [MEM] THEN
Cases_on `h` THEN
METIS_TAC [colouring_satisfactory_def])


val mem_after_map_conflicts = store_thm(
	"mem_after_map_conflicts", ``
! (x:num) (xs: num list) (c:num->(num # num list)) .
    MEM x xs ==> MEM (c x) (MAP c xs)``,
RW_TAC std_ss [MEM_MAP] THEN Q.EXISTS_TAC `x`
THEN EVAL_TAC THEN FULL_SIMP_TAC bool_ss [])

val colouring_satisfactory_expansion = store_thm(
	"colouring_satisfactory_expansion", ``
! code live (r:num) (col:num->num) .
colouring_satisfactory col (get_conflicts code live)
==> (! r . ~(MEM (col r) (MAP col (conflicts_for_register r code live))))
``,
RW_TAC std_ss [get_conflicts_def] THEN
Cases_on `MEM r (get_registers code live)` THEN1 (
	 `(r, conflicts_for_register r code live) =
	 (\reg . (reg, conflicts_for_register reg code live)) r`
	       by METIS_TAC [] THEN
	 ASSUME_TAC mem_after_map_conflicts THEN
	 Q.PAT_ASSUM `!x xs c . MEM x xs ==> MEM (c x) (MAP c xs)`
	 	     (ASSUME_TAC o Q.SPECL [`r`, `get_registers code live`,
		     `\reg . (reg, conflicts_for_register reg code live)`]) THEN
	 `MEM (r, conflicts_for_register r code live)
	      (MAP (\reg . (reg, conflicts_for_register reg code live))
	      (get_registers code live))`
	      by METIS_TAC [] THEN
	 `~(MEM (col r) (MAP col (conflicts_for_register r code live)))`
	 	by METIS_TAC [colouring_satisfactory_on_one_vertex]) THEN
`conflicts_for_register r code live = []`
			by METIS_TAC [unused_registers_do_not_conflict] THEN
FULL_SIMP_TAC bool_ss [] THEN
EVAL_TAC)


(* Proving that satisfying the constraints also satisfies colouring_ok *)
val satisfactory_colouring_is_ok = store_thm(
	"satisfactory_colouring_is_ok", ``
! c code live .
  duplicate_free live ==>
  colouring_satisfactory c (get_conflicts code live)
  ==> colouring_ok_alt c code live
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [colouring_ok_alt_def] THEN
FULL_SIMP_TAC bool_ss [colouring_respects_conflicting_sets_every] THEN
`(! r . ~(MEM (c r) (MAP c (conflicts_for_register r code live))))`
    by METIS_TAC [colouring_satisfactory_expansion] THEN
METIS_TAC [respecting_register_conflicts_respects_conflicting_sets])


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


val function_irrelevant_update = store_thm(
	"function_irrelevant_update", ``
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


val colouring_map_with_unused_update = store_thm(
	"colouring_map_with_unused_update", ``
! q r n cs .
~(MEM q r) ==>
(MAP ((q=+n) (naive_colouring_aux cs (n + 1))) r
=
MAP (naive_colouring_aux cs (n + 1)) r)
``,
REPEAT STRIP_TAC THEN
IMP_RES_TAC function_irrelevant_update THEN
METIS_TAC [function_irrelevant_update, naive_colouring_aux_def])



(* naive_colouring_aux starting from a register n+1 is always either equal
to naive_colouring_aux from register n or one greater than it *)
val naive_colouring_aux_equality = store_thm(
	"naive_colouring_aux_equality", ``
! cs n x .
((naive_colouring_aux cs (n + 1) x) = (naive_colouring_aux cs n x))
\/
((naive_colouring_aux cs (n + 1) x) = ((naive_colouring_aux cs n x) + 1))
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
Cases_on `h` THEN
EVAL_TAC THEN
Cases_on `q = x` THEN1 (FULL_SIMP_TAC bool_ss []) THEN
FULL_SIMP_TAC bool_ss [])

val naive_colouring_colours_greater_than_n = store_thm(
	"naive_colouring_colours_greater_than_n", ``
! (cs:(num # num list) list) (n:num) (x:num) .
(naive_colouring_aux cs (n+1) x) > n
``,
Induct_on `cs` THEN1 (REPEAT STRIP_TAC THEN EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
EVAL_TAC THEN
Cases_on `q = x` THEN1 (FULL_SIMP_TAC bool_ss [] THEN DECIDE_TAC) THEN
FULL_SIMP_TAC bool_ss [] THEN
`naive_colouring_aux cs (n + 1) x > n` by METIS_TAC [] THEN
`(naive_colouring_aux cs (n + 1 + 1) x = naive_colouring_aux cs (n + 1) x)
\/
(naive_colouring_aux cs (n + 1 + 1) x = (naive_colouring_aux cs (n + 1) x) + 1)`
by METIS_TAC [naive_colouring_aux_equality] THEN1 (METIS_TAC []) THEN
`naive_colouring_aux cs (n + 1) x + 1 > n` by FULL_SIMP_TAC arith_ss [] THEN
METIS_TAC [])

(* naive_colouring_aux starting from n+1 does not assign n *)
val naive_colouring_colours_all_new = store_thm(
	"naive_colouring_colours_all_new", ``
! (cs:(num # num list) list) (n:num) (x:num) .
(naive_colouring_aux cs (n+1)) (x) <> n
``,
REPEAT STRIP_TAC THEN
`naive_colouring_aux cs (n + 1) x > n`
by METIS_TAC [naive_colouring_colours_greater_than_n] THEN
DECIDE_TAC)



(* If a function is never equal to n, updating it so one value is mapped to
n does not make any other values map to n *)
val apply_update_only_changes_updated_value = store_thm(
	"apply_update_only_changes_updated_value", ``
! f n w .
(! x . f x <> n) ==> (! x . (x <> w) ==> (((w =+ n) f) x <> n))
``,
REPEAT STRIP_TAC THEN
Cases_on `x = w` THEN1 (FULL_SIMP_TAC std_ss []) THEN
`f x <> n` by METIS_TAC [] THEN
METIS_TAC [APPLY_UPDATE_THM])

(* If only one value 'x' maps to a particular output value 'n', mapping the
function over a list which does not contain x will give a list not containing
n *)
val map_output_only_contains_values_mapped_from_inputs = store_thm(
	"map_output_only_contains_values_mapped_from_inputs", ``
! x list f n .
~(MEM x list) /\ (! y . (y <> x) ==> (f y <> n))
==>
~(MEM n (MAP f list))
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
`~(MEM x list)` by METIS_TAC [MEM] THEN
`~(MEM n (MAP f list))` by METIS_TAC [] THEN
FULL_SIMP_TAC bool_ss [MEM, MAP] THEN
METIS_TAC [])



val input_unaffected_by_unrelated_update = store_thm(
	"input_unaffected_by_unrelated_update", ``
(((q =+ n) f) h <> (f h))
==> (h = q)
``,
REPEAT STRIP_TAC THEN
Cases_on `h = q` THEN1 FULL_SIMP_TAC bool_ss [] THEN
`((q =+ n) f) h = f h` by EVAL_TAC THEN
FULL_SIMP_TAC bool_ss [])

val output_cannot_exist_without_being_mapped_to = store_thm(
	"output_cannot_exist_without_being_mapped_to", ``
! f x list n q .
(~(MEM (f x) (MAP f list)) /\ (f x <> n))
==> ~(MEM (f x) (MAP ((q =+ n) f) list))
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
`~(MEM (f x) (MAP f list))` by METIS_TAC [MAP, MEM] THEN
`~(MEM (f x) (MAP ((q =+ n) f) list))` by METIS_TAC [] THEN
FULL_SIMP_TAC bool_ss [MAP, MEM] THEN
`h = q` by METIS_TAC [input_unaffected_by_unrelated_update] THEN
`(q =+ n) f h = n` by EVAL_TAC THEN
METIS_TAC [])


(* Updating a satisfactory colouring with a value unused by any register
yields another satisfactory colouring *)
val colouring_satisfactory_after_update = store_thm(
	"colouring_satisfactory_after_update", ``
! (c:num->num) (cs:(num # num list) list) (q:num) (n:num) .
  (graph_edge_lists_well_formed cs) /\
  colouring_satisfactory c cs /\ (! x . c x <> n)
  ==> colouring_satisfactory ((q =+ n) c) cs
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
EVAL_TAC THEN
Cases_on `q = q'` THEN1 (
	 FULL_SIMP_TAC bool_ss [] THEN
	 `~(MEM q' r)` by FULL_SIMP_TAC bool_ss
	 	[graph_edge_lists_well_formed_def,
		edge_list_well_formed_def, EVERY_DEF] THEN
	 `graph_edge_lists_well_formed cs`
	 	 by METIS_TAC [graph_edge_lists_well_formed_def,
		    EVERY_DEF] THEN
	 `colouring_satisfactory c cs`
	 	 by METIS_TAC [colouring_satisfactory_def] THEN
	 `colouring_satisfactory ((q' =+ n) c) cs` by METIS_TAC [] THEN
	 METIS_TAC [map_output_only_contains_values_mapped_from_inputs,
	 	   apply_update_only_changes_updated_value]) THEN
FULL_SIMP_TAC bool_ss [] THEN
`~(MEM q' r)` by FULL_SIMP_TAC bool_ss [graph_edge_lists_well_formed_def,
        edge_list_well_formed_def, EVERY_DEF] THEN
`graph_edge_lists_well_formed cs`
        by METIS_TAC [graph_edge_lists_well_formed_def, EVERY_DEF] THEN
`colouring_satisfactory c cs`
        by METIS_TAC [colouring_satisfactory_def] THEN
`colouring_satisfactory ((q' =+ n) c) cs` by METIS_TAC [] THEN
`~(MEM (c q') (MAP c r))` by METIS_TAC [colouring_satisfactory_def] THEN
`c q' <> n` by METIS_TAC [] THEN
METIS_TAC [output_cannot_exist_without_being_mapped_to])

(* A naive colouring is still satisfactory if it is updated with a value
unused by any register *)
val naive_colouring_satisfactory_with_unused_value = store_thm(
	"naive_colouring_satisfactory_with_unused_value", ``
! n cs q.
graph_edge_lists_well_formed cs /\
(colouring_satisfactory (naive_colouring_aux cs (n+1)) cs)
==>
(colouring_satisfactory ((q =+ n) (naive_colouring_aux cs (n+1))) cs)
``,
REPEAT STRIP_TAC THEN
`! x . naive_colouring_aux cs (n + 1) x <> n`
   by METIS_TAC [naive_colouring_colours_all_new] THEN
METIS_TAC [colouring_satisfactory_after_update])


val map_doesnt_contain_unused_values = store_thm(
	"map_doesnt_contain_unused_values", ``
    ! list f n .
    (!x . f x <> n) ==> ~(MEM n (MAP f list))
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
`~(MEM n (MAP f list))` by METIS_TAC [] THEN
FULL_SIMP_TAC std_ss [MAP, MEM] THEN
METIS_TAC [])

val naive_colouring_aux_satisfactory = store_thm(
	"naive_colouring_aux_satisfactory", ``
!(cs:(num # num list) list) .
graph_edge_lists_well_formed cs ==>
(! n . colouring_satisfactory (naive_colouring_aux cs n) cs)
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
Cases_on `h` THEN
EVAL_TAC THEN
STRIP_TAC THEN
STRIP_TAC THEN
STRIP_TAC THEN1 (
	  `graph_edge_lists_well_formed cs`
	          by METIS_TAC [graph_edge_lists_well_formed_def] THEN
	  `colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs`
	  by METIS_TAC [] THEN
	  (* now use the fact that the edge list is well-formed - need to add
	  this fact to the overall goal's assumptions *)
	  `~(MEM q r)` by METIS_TAC [graph_edge_lists_well_formed_def,
	  	 edge_list_well_formed_def, EVERY_DEF] THEN
	  `!x . (naive_colouring_aux cs (n + 1)) x <> n`
	  by METIS_TAC [naive_colouring_colours_all_new] THEN
	  FULL_SIMP_TAC std_ss [colouring_map_with_unused_update] THEN
	  METIS_TAC [map_doesnt_contain_unused_values])
THEN
`graph_edge_lists_well_formed cs`
        by METIS_TAC [graph_edge_lists_well_formed_def] THEN
`colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs` by METIS_TAC []
THEN METIS_TAC [naive_colouring_satisfactory_with_unused_value])


val naive_colouring_aux_satisfactory_implication = store_thm(
	"naive_colouring_aux_satisfactory_implication", ``
! (cs : (num # num list) list) .
(! (n:num) . colouring_satisfactory
    (naive_colouring_aux cs n) cs)
==> (colouring_satisfactory (naive_colouring cs) cs)
``,
REPEAT STRIP_TAC THEN
Cases_on `cs` THEN1 EVAL_TAC THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [naive_colouring_def])

val naive_colouring_satisfactory = store_thm(
	"naive_colouring_satisfactory", ``
!(cs:(num # num list) list) .
	  graph_edge_lists_well_formed cs ==>
	  colouring_satisfactory (naive_colouring cs) cs
``,
METIS_TAC [naive_colouring_aux_satisfactory,
	  naive_colouring_aux_satisfactory_implication])


val test = EVAL ``let cs = [(1, [2; 3]); (2, [1]); (3, [1])] in
colouring_satisfactory (naive_colouring cs) cs``



(* Determines whether a heuristic is acceptable *)
(*An acceptable heuristic only re-orders the input constraints *)
val heuristic_application_ok_def = Define `
    (heuristic_application_ok f = ! list . set (f list) = set (list))
`

val heuristic_insert_def = Define `
    (heuristic_insert f x [] = [x]) /\
    (heuristic_insert f x (y::ys) = if (f x > f y) then x::y::ys
    		      else y::(heuristic_insert f x ys))
`

val heuristic_sort_def = Define	`
    (heuristic_sort (f:(num # num list)->num) [] = []) /\
    (heuristic_sort f (x::xs) = (heuristic_insert f x (heuristic_sort f xs)))
`

val sort_heuristic_ok_def = Define `
    (sort_heuristic_ok (f:(num # num list)->num) =
    ! (list:(num # num list) list) . set (heuristic_sort f list) = set (list))
`

val sort_heuristic_ok_IMP_heuristic_application_ok = store_thm(
	"sort_heuristic_ok_IMP_heuristic_application_ok", ``
! f . sort_heuristic_ok f ==> heuristic_application_ok (heuristic_sort f)
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [sort_heuristic_ok_def, heuristic_application_ok_def])

val insert_adds_correctly = prove(``
! f x ys . MEM x (heuristic_insert f x ys)
``,
Induct_on `ys` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
EVAL_TAC THEN
Cases_on `f x > f h` THEN1 (FULL_SIMP_TAC bool_ss [] THEN EVAL_TAC) THEN
FULL_SIMP_TAC bool_ss [] THEN
`MEM x (heuristic_insert f x ys)` by METIS_TAC [] THEN
EVAL_TAC THEN METIS_TAC [])


val set_after_heuristic_insert = store_thm("set_after_heuristic_insert",
``
! f h list .
set (heuristic_insert f h list) = {h} UNION (set list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN
	  METIS_TAC [LIST_TO_SET, SUBSET_REFL, EMPTY_SUBSET]) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [heuristic_insert_def] THEN
Cases_on `f h' > f h` THEN1 (
	 FULL_SIMP_TAC bool_ss [] THEN
	 METIS_TAC [LIST_TO_SET, INSERT_SING_UNION]) THEN
FULL_SIMP_TAC bool_ss [] THEN
`set (heuristic_insert f h' list) = ({h'} UNION (set list))`
     by METIS_TAC [] THEN
FULL_SIMP_TAC bool_ss [LIST_TO_SET] THEN
`{h'} UNION (h INSERT set list) = h INSERT ({h'} UNION set list)`
by METIS_TAC [INSERT_SING_UNION, UNION_EMPTY, UNION_ASSOC, UNION_COMM] THEN
METIS_TAC [])


val all_heuristic_sorts_ok = store_thm("all_heuristic_sorts_ok",
``
! (f:(num # num list)->num) . sort_heuristic_ok f
``,
FULL_SIMP_TAC std_ss [sort_heuristic_ok_def] THEN
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [heuristic_sort_def] THEN
`set (heuristic_sort f list) = set list` by METIS_TAC [] THEN
`set (heuristic_insert f h (heuristic_sort f list)) =
     {h} UNION (set (heuristic_sort f list))`
     by METIS_TAC [set_after_heuristic_insert] THEN
`set (h::list) = {h} UNION set (list)`
     by METIS_TAC [LIST_TO_SET, INSERT_SING_UNION] THEN
METIS_TAC [])


val vertex_degree_def = Define `
    (vertex_degree (_, []) = 0) /\
    (vertex_degree (r, (x::xs)) = (vertex_degree (r, xs)) + 1)
`

val highest_degree_correctness = store_thm("highest_degree_correctness",
``sort_heuristic_ok vertex_degree``, METIS_TAC [all_heuristic_sorts_ok])


(* Heuristic which selects the vertex with lowest degree in the subgraph of
vertices not considered each time *)

(* Get the degree of a vertex ignoring those contained in the set 'done' *)
val vertex_degree_in_subgraph_def = Define `
    (vertex_degree_in_subgraph done (v, []) = 0) /\
    (vertex_degree_in_subgraph done (v, (e::es)) =
        if (done e) then (vertex_degree_in_subgraph done (v, es))
	else SUC (vertex_degree_in_subgraph done (v, es)))
`

(* Sorts the list of conflicts according to degree in the subgraph where those
already considered have been removed *)
val sort_not_considered_by_degree_def = Define `
    (sort_not_considered_by_degree
        (done:num->bool) (list:(num # num list) list) =
	QSORT (\ x y . (vertex_degree_in_subgraph done x)
	      < (vertex_degree_in_subgraph done y) /\
	      ~(done (FST x))) list)
`

(* Handy lemma regarding set equality: two sets made from lists are equal iff
being a member of one list is equivalent to being a member of the other *)
val set_list_equality = store_thm("set_list_equality",
``
! list list' .
(! x . MEM x list = MEM x list') ==>
(set list = set list')
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SET_EQ_SUBSET] THEN
STRIP_TAC THEN FULL_SIMP_TAC std_ss [SUBSET_DEF])


(* The heuristic itself *)
(* done is the list of vertices already considered, which are to be treated as
having been removed from the graph. sort_not_considered_by_degree ignores
vertices included in done *)
(* cs' is the stack of vertices being build up, and is reversed at the end so it
is considered in the correct order (colouring works back-to-front) *)
(* Note that the algorithm assumes the list passed in as the second argument is
sorted *)
val lowest_degree_subgraph_heuristic_aux_def = tDefine
    "lowest_degree_subgraph_heuristic_aux" `
    (lowest_degree_subgraph_heuristic_aux done [] cs' = REVERSE cs') /\
    (lowest_degree_subgraph_heuristic_aux done ((r, rs)::cs) cs' =
        let sorted = (sort_not_considered_by_degree (r INSERT done) cs) in
        lowest_degree_subgraph_heuristic_aux
		(r INSERT done) sorted ((r, rs)::cs'))
` (WF_REL_TAC ` measure (\ (done, cs, cs') . LENGTH cs)` THEN
`! done cs . LENGTH (sort_not_considered_by_degree done cs) =
LENGTH (cs)` by cheat THEN
FULL_SIMP_TAC arith_ss [LENGTH])

val lowest_degree_subgraph_heuristic_aux_ind = DB.fetch "-"
    "lowest_degree_subgraph_heuristic_aux_ind"

val lowest_degree_subgraph_heuristic_def = Define `
    (lowest_degree_subgraph_heuristic cs =
        lowest_degree_subgraph_heuristic_aux (\x . F)
	    (sort_not_considered_by_degree (\x . F) cs) [])
`


(* The function sort_not_considered_by_degree_ok maintains the set which is
passed in *)
val sort_not_considered_by_degree_ok = store_thm(
    "sort_not_considered_by_degree_ok", ``
! list done .
set list = set (sort_not_considered_by_degree done list)
``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [sort_not_considered_by_degree_def] THEN
METIS_TAC [QSORT_MEM, set_list_equality])

(* All values belonging to the accumulator variable in a call to
lowest_degree_subgraph_heuristic_aux will feature in the result *)
val acc_returned = store_thm("acc_returned", ``
! done list acc .
MEM x acc ==> MEM x (lowest_degree_subgraph_heuristic_aux done list acc)
``,
recInduct lowest_degree_subgraph_heuristic_aux_ind THEN
STRIP_TAC THEN1 (
    FULL_SIMP_TAC std_ss [lowest_degree_subgraph_heuristic_aux_def] THEN
    METIS_TAC [LIST_TO_SET_REVERSE]) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [LET_DEF] THEN
`MEM x ((r, rs)::cs')` by METIS_TAC [MEM] THEN
FULL_SIMP_TAC bool_ss [lowest_degree_subgraph_heuristic_aux_def] THEN
FULL_SIMP_TAC bool_ss [LET_DEF])

(* Being a member of the result of sorting with the lowest-degree subgraph
heuristic is equivalent to being a member of the original list or of the
accumulator variable passed in *)
val lowest_degree_subgraph_heuristic_aux_MEM = store_thm(
    "lowest_degree_subgraph_heuristic_aux_MEM", ``
! done list acc .
MEM x list \/ MEM x acc
= MEM x (lowest_degree_subgraph_heuristic_aux done list acc)
``,
recInduct lowest_degree_subgraph_heuristic_aux_ind THEN
STRIP_TAC THEN1 (
    FULL_SIMP_TAC bool_ss [lowest_degree_subgraph_heuristic_aux_def,
        MEM] THEN
    METIS_TAC [LIST_TO_SET_REVERSE]) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [] THEN
Cases_on `x = (r,rs)` THEN1 (
	 FULL_SIMP_TAC bool_ss [MEM] THEN
	 FULL_SIMP_TAC bool_ss [lowest_degree_subgraph_heuristic_aux_def] THEN
	 FULL_SIMP_TAC bool_ss [LET_DEF]) THEN
Cases_on `MEM x cs'` THEN1 (METIS_TAC [acc_returned]) THEN
FULL_SIMP_TAC bool_ss [MEM] THEN
Cases_on `MEM x cs` THEN1 (
	 FULL_SIMP_TAC bool_ss [] THEN
	 `MEM x (sort_not_considered_by_degree (r INSERT done) cs)`
	      by METIS_TAC [sort_not_considered_by_degree_ok] THEN
	  FULL_SIMP_TAC bool_ss [lowest_degree_subgraph_heuristic_aux_def] THEN
	  FULL_SIMP_TAC bool_ss [LET_DEF]) THEN
FULL_SIMP_TAC bool_ss [] THEN
STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [lowest_degree_subgraph_heuristic_aux_def] THEN
FULL_SIMP_TAC bool_ss [LET_DEF] THEN
`~(MEM x (sort_not_considered_by_degree (r INSERT done) cs))`
       by METIS_TAC [sort_not_considered_by_degree_ok])

(* The lowest-degree subgraph heuristic satisfies heuristic_application_ok *)
val lowest_degree_subgraph_heuristic_ok = store_thm(
    "lowest_degree_subgraph_heuristic_ok", ``
heuristic_application_ok lowest_degree_subgraph_heuristic
``,
FULL_SIMP_TAC std_ss [heuristic_application_ok_def,
	      lowest_degree_subgraph_heuristic_def] THEN
REPEAT STRIP_TAC THEN
`! x . MEM x (sort_not_considered_by_degree (\x. F) list)
   = MEM x list` by cheat THEN
`! x . MEM x (sort_not_considered_by_degree (\x. F) list) \/ MEM x []
     = MEM x (lowest_degree_subgraph_heuristic_aux (\x. F)
       (sort_not_considered_by_degree (\x. F) list) [])`
    by METIS_TAC [lowest_degree_subgraph_heuristic_aux_MEM] THEN
`! x . MEM x (sort_not_considered_by_degree (\x. F) list)
    = MEM x (lowest_degree_subgraph_heuristic_aux (\x. F)
       (sort_not_considered_by_degree (\x. F) list) [])` by ALL_TAC THEN1 (
    REPEAT STRIP_TAC THEN
    Cases_on `MEM x (sort_not_considered_by_degree (\x . F) list)` THEN1 (
        FULL_SIMP_TAC bool_ss [] THEN
	METIS_TAC []) THEN
    FULL_SIMP_TAC bool_ss [] THEN
    STRIP_TAC THEN
    `MEM x (sort_not_considered_by_degree (\x. F) list) \/ MEM x []`
    by METIS_TAC [] THEN
    `~(MEM x [])` by METIS_TAC [MEM]) THEN
`! x . MEM x (lowest_degree_subgraph_heuristic_aux (\x. F)
         (sort_not_considered_by_degree (\x. F) list) [])
    = MEM x list` by METIS_TAC [] THEN
METIS_TAC [set_list_equality])


(* Most-used-first heuristic: ensures that registers used most are at the back
of the list and so get coloured first, meaning those which are used a lot will
be prioritised when spilling occurs *)
val most_used_last_heuristic_def = Define `
    (most_used_last_heuristic uses list =
    		    QSORT (\x y . uses x < uses y) list)
`

val most_used_last_heuristic_ok = store_thm("most_used_last_heuristic_ok",
``
! uses .
heuristic_application_ok (most_used_last_heuristic uses)
``,
FULL_SIMP_TAC bool_ss [heuristic_application_ok_def,
	      most_used_last_heuristic_def] THEN
REPEAT STRIP_TAC THEN
METIS_TAC [set_list_equality, QSORT_MEM])



(* Lowest-first colouring:
Take the supplied constraints in order, and assign to each register the
lowest colour which doesn't conflict *)

(* Maximum of a list *)
val list_max = Define `
    (list_max [] = 0) /\
    (list_max (x::xs) = let tail = list_max xs in
    (if x > tail then x else tail))
`

val list_max_is_largest = store_thm("list_max_is_largest",
``
    ! x list . MEM x list ==> (x <= list_max list)
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
Cases_on `h > list_max list` THEN1(
        FULL_SIMP_TAC bool_ss [] THEN
        Cases_on `x = h` THEN1 (FULL_SIMP_TAC arith_ss [MEM]) THEN
		FULL_SIMP_TAC arith_ss [MEM] THEN
		`x <= list_max list` by METIS_TAC [] THEN
		FULL_SIMP_TAC arith_ss []
        ) THEN
FULL_SIMP_TAC arith_ss [] THEN
Cases_on `x = h` THEN1 (FULL_SIMP_TAC arith_ss [MEM]) THEN
FULL_SIMP_TAC arith_ss [MEM])

(* Find the smallest value which is not a member of a list *)
val smallest_nonmember_def = tDefine "smallest_nonmember" `
    (smallest_nonmember x list = if (MEM x list)
    			then smallest_nonmember (x + 1) list
			else x)
` (WF_REL_TAC ` measure (\(x, ys) . ((list_max ys) + 1) - x)` THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC arith_ss [] THEN
`x <= list_max list` by METIS_TAC [list_max_is_largest] THEN
FULL_SIMP_TAC arith_ss [])

val smallest_nonmember_ind = DB.fetch "-" "smallest_nonmember_ind";


val smallest_nonmember_is_not_member = store_thm(
	"smallest_nonmember_is_not_member", ``
! n list . ~(MEM (smallest_nonmember n list) list)
``,
recInduct smallest_nonmember_ind THEN
REPEAT STRIP_TAC THEN
Cases_on `MEM x list` THEN
METIS_TAC [smallest_nonmember_def] THEN
METIS_TAC [smallest_nonmember_def])


(* Finds the lowest available colour given a colouring and a set of clashing
registers *)
val lowest_available_colour_def = Define `
    (lowest_available_colour (col:num->num) cs =
    			     smallest_nonmember 0 (MAP col cs))
`
val lowest_available_colour_is_valid = store_thm(
	"lowest_available_colour_is_valid", ``
! col cs . ~(MEM (lowest_available_colour col cs) (MAP col cs))
``,
FULL_SIMP_TAC bool_ss [lowest_available_colour_def] THEN
METIS_TAC [smallest_nonmember_is_not_member])


(* Computes a lowest-first colouring for the supplied graph *)
val lowest_first_colouring_def = Define `
    (lowest_first_colouring [] = \x.0) /\
    (lowest_first_colouring ((r, rs)::cs) =
        let (col:num->num) = (lowest_first_colouring cs) in
	let lowest_available = (lowest_available_colour col rs) in
	(r =+ lowest_available) col)
`


val colouring_satisfactory_every = prove(``
! col cs .
(colouring_satisfactory col cs) =
(EVERY (\ (x, xs) . ~(MEM(col x) (MAP col xs))) cs)
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
EVAL_TAC THEN
METIS_TAC [])

(* The lemma for proving lowest-first colouring is correct. Essentially, if
a colouring update satisfies the constraints for the current vertex then it
satisfies those of all vertices which have already been examined. This follows
from the fact that a graph won't have duplicate vertices and each conflict
list contains all conflicts for a register *)
val new_colour_satisfactory_if_constraints_satisfied = store_thm(
	"new_colour_satisfactory_if_constraints_satisfied", ``
! (n:num) (r:num) (col:num->num) (rs:num list) (cs: (num # num list) list) .
(graph_reflects_conflicts ((r,rs)::cs)) /\
(graph_duplicate_free ((r, rs)::cs)) /\
(~(MEM n (MAP ((r =+ n) col) rs)) /\ (colouring_satisfactory col cs))
==>
(colouring_satisfactory ((r =+ n)col) ((r, rs)::cs))
``,
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
FULL_SIMP_TAC bool_ss [] THEN
FULL_SIMP_TAC bool_ss [colouring_satisfactory_every] THEN
(* TODO use duplicate-freeness for next line *)
`! y ys . MEM (y, ys) cs ==> y <> r` by cheat THEN
FULL_SIMP_TAC bool_ss [EVERY_MEM] THEN
REPEAT STRIP_TAC THEN
Cases_on `e` THEN
`q <> r` by METIS_TAC [MEM] THEN
EVAL_TAC THEN
FULL_SIMP_TAC bool_ss [] THEN
(* TODO the below follows by implication in assumptions *)
`~(MEM (col q) (MAP col r'))` by cheat THEN
Tactical.REVERSE (Cases_on `MEM r r'`) THEN1
    METIS_TAC [function_irrelevant_update] THEN
Tactical.REVERSE(`col q <> n` by ALL_TAC) THEN1
    METIS_TAC [output_cannot_exist_without_being_mapped_to] THEN
`MEM (r, rs) ((r,rs)::cs) /\ MEM (q,r') ((r,rs)::cs)`
     by FULL_SIMP_TAC bool_ss [MEM] THEN
`MEM q rs` by METIS_TAC [graph_reflects_conflicts_def] THEN
`MEM ((r=+n)col q) (MAP ((r=+n)col) rs)` by METIS_TAC [mem_after_map] THEN
`((r=+n)col) q = col q` by FULL_SIMP_TAC bool_ss [UPDATE_APPLY] THEN
FULL_SIMP_TAC bool_ss [] THEN
METIS_TAC [])


val lowest_first_colouring_satisfactory = store_thm(
	"lowest_first_colouring_satisfactory", ``
! cs .
  graph_reflects_conflicts cs /\
  graph_duplicate_free cs /\
  graph_edge_lists_well_formed cs ==>
  colouring_satisfactory (lowest_first_colouring cs) cs
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
`graph_edge_lists_well_formed cs`
        by METIS_TAC [graph_edge_lists_well_formed_def, EVERY_DEF] THEN
`graph_duplicate_free cs` by METIS_TAC [graph_duplicate_free_def] THEN
`graph_reflects_conflicts cs`
    by METIS_TAC [graph_reflects_conflicts_preserved] THEN
`colouring_satisfactory (lowest_first_colouring cs) cs` by METIS_TAC [] THEN
TACTICAL.REVERSE (`~(MEM (lowest_available_colour (lowest_first_colouring cs) r)
       (MAP ((q =+ lowest_available_colour (lowest_first_colouring cs) r)
       (lowest_first_colouring cs)) r))` by ALL_TAC) THEN1 (
       FULL_SIMP_TAC std_ss [lowest_first_colouring_def] THEN
       FULL_SIMP_TAC bool_ss [LET_DEF] THEN
       METIS_TAC [new_colour_satisfactory_if_constraints_satisfied]) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM] THEN
`~(MEM q r)` by METIS_TAC [graph_edge_lists_well_formed_def,
       edge_list_well_formed_def, EVERY_DEF] THEN
METIS_TAC [function_irrelevant_update, lowest_available_colour_is_valid])



(* Lowest-first colouring which also takes into account a preference list for
each register *)

(* Select the first preference which can be satisfied, or 0 if none can be
satisfied *)
val best_preference_colour_def = Define `
    (best_preference_colour col rs [] = 0) /\
    (best_preference_colour col rs (p::ps) = if ~(MEM (col p) rs) then (col p)
    			    else (best_preference_colour col rs ps))
`

(* Colour the graph satisfying each vertice's preferences wherever possible and
defaulting to lowest-first colouring where preferences cannot be satisfied *)
val lowest_first_preference_colouring_def = Define `
    (lowest_first_preference_colouring [] (prefs:num->(num list)) = \x.0) /\
    (lowest_first_preference_colouring ((r, rs)::cs) prefs =
        let (col:num->num) = (lowest_first_preference_colouring cs prefs) in
	let lowest_available = (lowest_available_colour col rs) in
	let preference_colour = (best_preference_colour col rs (prefs r)) in
	    if ~(MEM preference_colour (MAP col rs)) then
	       ((r =+ preference_colour) col)
            else
		((r =+ lowest_available) col)
    )
`


(* Lowest-first colouring with a preference graph is satisfactory *)
val lowest_first_preference_colouring_satisfactory = store_thm(
	"lowest_first_preference_colouring_satisfactory", ``
! cs prefs .
  graph_reflects_conflicts cs /\
  graph_duplicate_free cs /\
  graph_edge_lists_well_formed cs ==>
  colouring_satisfactory (lowest_first_preference_colouring cs prefs) cs
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
`graph_edge_lists_well_formed cs`
        by METIS_TAC [graph_edge_lists_well_formed_def, EVERY_DEF] THEN
`graph_duplicate_free cs` by METIS_TAC [graph_duplicate_free_def] THEN
`graph_reflects_conflicts cs`
    by METIS_TAC [graph_reflects_conflicts_preserved] THEN
`colouring_satisfactory (lowest_first_preference_colouring cs prefs) cs`
			by METIS_TAC [] THEN
`~(MEM (lowest_available_colour (lowest_first_preference_colouring cs prefs) r)
(MAP ((q =+ lowest_available_colour
     (lowest_first_preference_colouring cs prefs) r)
(lowest_first_preference_colouring cs prefs)) r))` by ALL_TAC THEN1 (
        REPEAT STRIP_TAC THEN
	FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM] THEN
	`~(MEM q r)` by METIS_TAC [graph_edge_lists_well_formed_def,
	        edge_list_well_formed_def, EVERY_DEF] THEN
        METIS_TAC [function_irrelevant_update,
	        lowest_available_colour_is_valid]) THEN
FULL_SIMP_TAC std_ss [lowest_first_preference_colouring_def] THEN
FULL_SIMP_TAC std_ss [LET_DEF] THEN
Cases_on `(MEM
(best_preference_colour
	(lowest_first_preference_colouring cs prefs) r (prefs q))
(MAP (lowest_first_preference_colouring cs prefs) r))` THEN1 (
     FULL_SIMP_TAC bool_ss [] THEN
     METIS_TAC [new_colour_satisfactory_if_constraints_satisfied]) THEN
FULL_SIMP_TAC bool_ss [] THEN
(* TODO: This next thing is very similar to the thing proved earlier and also in
the proof of lowest_first correctness - see if it can be extracted to a
lemma? *)
TACTICAL.REVERSE (`~(MEM
(best_preference_colour
	(lowest_first_preference_colouring cs prefs) r (prefs q))
(MAP ((q =+
(best_preference_colour
	(lowest_first_preference_colouring cs prefs) r (prefs q)))
(lowest_first_preference_colouring cs prefs)) r))
` by ALL_TAC) THEN1 (
  METIS_TAC [new_colour_satisfactory_if_constraints_satisfied]) THEN
`~(MEM q r)` by METIS_TAC [graph_edge_lists_well_formed_def,
       edge_list_well_formed_def, EVERY_DEF] THEN
METIS_TAC [function_irrelevant_update, lowest_available_colour_is_valid])

val _ = export_theory();