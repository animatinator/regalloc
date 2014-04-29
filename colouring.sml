open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory
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
val no_duplicate_vertices_def = Define `
    (no_duplicate_vertices graph = duplicate_free (get_vertices graph))
`

(* Vertex is not linked to itself *)
val edge_list_well_formed_def = Define `
    (edge_list_well_formed ((v:num), (edges:num list)) = ~(MEM v edges)
    			   /\ duplicate_free edges)
`

(* Vertices in graph are not linked to themselves *)
val graph_edge_lists_well_formed_def = Define `
    (graph_edge_lists_well_formed [] = T) /\
    (graph_edge_lists_well_formed (e::es) = edge_list_well_formed e
    				  /\ graph_edge_lists_well_formed es)
`

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



(* naive_colouring_aux starting from a register n+1 is always either equal
to naive_colouring_aux from register n or one greater than it *)
val naive_colouring_aux_equality = prove(``
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

val naive_colouring_colours_greater_than_n = prove(``
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
val naive_colouring_colours_all_new = prove(``
! (cs:(num # num list) list) (n:num) (x:num) .
(naive_colouring_aux cs (n+1)) (x) <> n
``,
REPEAT STRIP_TAC THEN
`naive_colouring_aux cs (n + 1) x > n`
by METIS_TAC [naive_colouring_colours_greater_than_n] THEN
DECIDE_TAC)



(* If a function is never equal to n, updating it so one value is mapped to
n does not make any other values map to n *)
val apply_update_only_changes_updated_value = prove(``
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
val map_output_only_contains_values_mapped_from_inputs = prove(``
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



val input_unaffected_by_unrelated_update = prove(``
(((q =+ n) f) h <> (f h))
==> (h = q)
``,
REPEAT STRIP_TAC THEN
Cases_on `h = q` THEN1 FULL_SIMP_TAC bool_ss [] THEN
`((q =+ n) f) h = f h` by EVAL_TAC THEN
FULL_SIMP_TAC bool_ss [])

val output_cannot_exist_without_being_mapped_to = prove(``
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
val colouring_satisfactory_after_update = prove(``
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
		edge_list_well_formed_def] THEN
	 `graph_edge_lists_well_formed cs`
	 	 by METIS_TAC [graph_edge_lists_well_formed_def] THEN
	 `colouring_satisfactory c cs`
	 	 by METIS_TAC [colouring_satisfactory_def] THEN
	 `colouring_satisfactory ((q' =+ n) c) cs` by METIS_TAC [] THEN
	 METIS_TAC [map_output_only_contains_values_mapped_from_inputs,
	 	   apply_update_only_changes_updated_value]) THEN
FULL_SIMP_TAC bool_ss [] THEN
`~(MEM q' r)` by FULL_SIMP_TAC bool_ss [graph_edge_lists_well_formed_def,
        edge_list_well_formed_def] THEN
`graph_edge_lists_well_formed cs`
        by METIS_TAC [graph_edge_lists_well_formed_def] THEN
`colouring_satisfactory c cs`
        by METIS_TAC [colouring_satisfactory_def] THEN
`colouring_satisfactory ((q' =+ n) c) cs` by METIS_TAC [] THEN
`~(MEM (c q') (MAP c r))` by METIS_TAC [colouring_satisfactory_def] THEN
`c q' <> n` by METIS_TAC [] THEN
METIS_TAC [output_cannot_exist_without_being_mapped_to])

(* A naive colouring is still satisfactory if it is updated with a value
unused by any register *)
val naive_colouring_satisfactory_with_unused_value = prove(``
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


val map_doesnt_contain_unused_values = prove(``
    ! list f n .
    (!x . f x <> n) ==> ~(MEM n (MAP f list))
``,
Induct_on `list` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
`~(MEM n (MAP f list))` by METIS_TAC [] THEN
FULL_SIMP_TAC std_ss [MAP, MEM] THEN
METIS_TAC [])

val naive_colouring_aux_satisfactory = prove(``
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
	  `colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs`
	  by METIS_TAC [] THEN
	  (* now use the fact that the edge list is well-formed - need to add
	  this fact to the overall goal's assumptions *)
	  `~(MEM q r)` by METIS_TAC [graph_edge_lists_well_formed_def,
	  	 edge_list_well_formed_def] THEN
	  `!x . (naive_colouring_aux cs (n + 1)) x <> n`
	  by METIS_TAC [naive_colouring_colours_all_new] THEN
	  FULL_SIMP_TAC std_ss [colouring_map_with_unused_update] THEN
	  METIS_TAC [map_doesnt_contain_unused_values])
THEN
`colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs` by METIS_TAC []
THEN METIS_TAC [naive_colouring_satisfactory_with_unused_value])


val naive_colouring_aux_satisfactory_implication = prove(``
! (cs : (num # num list) list) .
(! (n:num) . colouring_satisfactory
    (naive_colouring_aux cs n) cs)
==> (colouring_satisfactory (naive_colouring cs) cs)
``,
REPEAT STRIP_TAC THEN
Cases_on `cs` THEN1 EVAL_TAC THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [naive_colouring_def])

val naive_colouring_satisfactory = prove(``
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

val heuristic_ok_def = Define `
    (heuristic_ok (f:(num # num list)->num) =
    ! (list:(num # num list) list) . set (heuristic_sort f list) = set (list))
`

val insert_adds_correctly = prove(``
! f x ys . MEM x (heuristic_insert f x ys)
``,
Induct_on `ys` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
EVAL_TAC THEN
Cases_on `f x > f h` THEN1 (FULL_SIMP_TAC bool_ss [] THEN EVAL_TAC) THEN
FULL_SIMP_TAC bool_ss [] THEN
`MEM x (heuristic_insert f x ys)` by METIS_TAC [] THEN
EVAL_TAC THEN METIS_TAC [])


val set_after_heuristic_insert = prove(``
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


val all_heuristic_sorts_ok = prove(``
! (f:(num # num list)->num) . heuristic_ok f
``,
FULL_SIMP_TAC std_ss [heuristic_ok_def] THEN
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


val highest_degree_def = Define `
    (highest_degree (_, []) = 0) /\
    (highest_degree (r, (x::xs)) = (highest_degree (r, xs)) + 1)
`

val highest_degree_correctness = prove(``heuristic_ok highest_degree``,
    METIS_TAC [all_heuristic_sorts_ok])



(* Lowest-first colouring:
Take the supplied constraints in order, and assign to each register the
lowest colour which doesn't conflict *)

(* Maximum of a list *)
val list_max = Define `
    (list_max [] = 0) /\
    (list_max (x::xs) = let tail = list_max xs in
    (if x > tail then x else tail))
`

val list_max_is_largest = prove(``
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


val smallest_nonmember_is_not_member = prove(``
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
val lowest_available_colour_is_valid = prove(``
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


(* Possible lemma for proving lowest-first correctness - not sure how to prove
it.
The problem is that (colouring_satisfactory col ((r,rs)::cs)) consists of
two goals:
    ~(MEM (col r) (MAP col rs))
    colouring_satisfactory col cs

The first is usually quite straightforward to prove, but the second is trickier
because the colouring 'col' is usually of the form ((q =+ n) col), but the
induction hypothesis only gives colouring_satisfactory col cs.
What I'm trying to do with this lemma is show that if the first goal holds of
((q =+ n) col), then the update (q =+ n) will be fine for the remainder of cs
(as intuitively (r, rs) should capture all the registers r clashes with, but
I'm not sure how to formalise this).
*)
val new_colour_satisfactory_if_constraints_satisfied = prove(``
! (n:num) (r:num) (col:num->num) (rs:num list) (cs: (num # num list) list) .
(~(MEM n (MAP ((r =+ n) col) rs)) /\ (colouring_satisfactory col cs))
==>
(colouring_satisfactory ((r =+ n)col) ((r, rs)::cs))
``,
REPEAT STRIP_TAC THEN
EVAL_TAC THEN
FULL_SIMP_TAC bool_ss [] THEN
cheat)


val lowest_first_colouring_satisfactory = prove(``
! cs .
  graph_edge_lists_well_formed cs ==>
  colouring_satisfactory (lowest_first_colouring cs) cs
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h` THEN
`graph_edge_lists_well_formed cs`
        by METIS_TAC [graph_edge_lists_well_formed_def] THEN
`colouring_satisfactory (lowest_first_colouring cs) cs` by METIS_TAC [] THEN
REVERSE (`~(MEM (lowest_available_colour (lowest_first_colouring cs) r)
       (MAP ((q =+ lowest_available_colour (lowest_first_colouring cs) r)
       (lowest_first_colouring cs)) r))` by ALL_TAC) THEN1 (
       FULL_SIMP_TAC std_ss [lowest_first_colouring_def] THEN
       FULL_SIMP_TAC bool_ss [LET_DEF] THEN
       METIS_TAC [new_colour_satisfactory_if_constraints_satisfied]) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM] THEN
`~(MEM q r)` by METIS_TAC [graph_edge_lists_well_formed_def,
       edge_list_well_formed_def] THEN
METIS_TAC [function_irrelevant_update, lowest_available_colour_is_valid])