open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory;

open three_addrTheory;


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
    (edge_list_well_formed (v, [edges]) = ~(MEM v edges))
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

(* Simplified version of colouring satisfying constraints:
Colouring satisfies top constraint *)
val colouring_satisfactory_top_def = Define `
    (colouring_satisfactory col [] = T) /\
    (colouring_satisfactory col ((r, rs)::cs) = ~(MEM (col r) (MAP col rs)))
`


``
! col r rs cs n .
colouring_satisfactory ((r =+ n)col) cs /\
(! x . col x <> n)
==>
colouring_satisfactory col cs
``
Induct_on `cs`
REPEAT STRIP_TAC THEN EVAL_TAC
REPEAT STRIP_TAC
Cases_on `h`
FULL_SIMP_TAC std_ss [colouring_satisfactory_def]
`colouring_satisfactory col cs` by METIS_TAC []
FULL_SIMP_TAC bool_ss []

Cases_on `q = r`
cheat
`(r =+ n) col q = col q` by EVAL_TAC THEN FULL_SIMP_TAC bool_ss []
FULL_SIMP_TAC std_ss []
cheat


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

(* This goal seems like the crux of the next goal *)
val naive_colouring_colours_all_new = prove(``
! (cs:(num # num list) list) (n:num) (x:num) .
(naive_colouring_aux cs (n+1)) (x) <> n
``,
REPEAT STRIP_TAC THEN
`naive_colouring_aux cs (n + 1) x > n`
by METIS_TAC [naive_colouring_colours_greater_than_n] THEN
DECIDE_TAC)



(* This next goal is the main missing part of the proof: *)
val naive_colouring_satisfactory_with_unused_value = prove(``
! n cs q.
(colouring_satisfactory (naive_colouring_aux cs (n+1)) cs)
==>
(colouring_satisfactory ((q =+ n) (naive_colouring_aux cs (n+1))) cs)
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
REPEAT STRIP_TAC THEN
Cases_on `h`
`colouring_satisfactory (naive_colouring_aux ((q', r)::cs) (n + 1)) cs` by METIS_TAC [colouring_satisfactory_def]
`colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs` by cheat
`colouring_satisfactory ((q =+ n) (naive_colouring_aux cs (n + 1))) cs` by METIS_TAC []
FULL_SIMP_TAC bool_ss [naive_colouring_aux_def]
FULL_SIMP_TAC bool_ss [colouring_satisfactory_def]
cheat)



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
!(cs:(num # num list) list) (n:num) . colouring_satisfactory (naive_colouring_aux cs n) cs
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
Cases_on `h` THEN
EVAL_TAC THEN
STRIP_TAC THEN
STRIP_TAC THEN1 (
	  `colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs`
	  by METIS_TAC [] THEN
	  (* now use the fact that the edge list is well-formed - need to add
	  this fact to the overall goal's assumptions *)
	  `~(MEM q r)` by cheat THEN
	  `!x . (naive_colouring_aux cs (n + 1)) x <> n`
	  by METIS_TAC [naive_colouring_colours_all_new] THEN
	  FULL_SIMP_TAC std_ss [colouring_map_with_unused_update] THEN
	  METIS_TAC [map_doesnt_contain_unused_values])
THEN
`colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs` by METIS_TAC []
THEN METIS_TAC [naive_colouring_satisfactory_with_unused_value])


val naive_colouring_aux_satisfactory_implication = prove(``
(!(cs:('a # 'a list) list) n . colouring_satisfactory
    (naive_colouring_aux cs n) cs)
==> (!(cs:('a # 'a list) list) n . colouring_satisfactory
    (naive_colouring cs) cs)
``,
REPEAT STRIP_TAC THEN
Cases_on `cs` THEN1 EVAL_TAC THEN
Cases_on `h` THEN
FULL_SIMP_TAC bool_ss [naive_colouring_def])

val naive_colouring_satisfactory = prove(``
!(cs:(num # num list) list) .
	  colouring_satisfactory (naive_colouring cs) cs
``,
METIS_TAC [naive_colouring_aux_satisfactory,
	  naive_colouring_aux_satisfactory_implication])


val test = EVAL ``let cs = [(1, [2; 3]); (2, [1]); (3, [1])] in
colouring_satisfactory (naive_colouring cs) cs``


(* Determines whether a heuristic is acceptable
(*An acceptable heuristic only re-orders the input constraints *)
val heuristic_ok_def = Define `
    (heuristic_ok f 
`*)