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



(* This goal seems like the crux of the next goal *)
val naive_colouring_colours_all_new = prove(``
! (cs:(num # num) list) (n:num) (x:num) .
(naive_colouring_aux cs (n+1)) (x) <> n
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
Cases_on `h` THEN
EVAL_TAC THEN
Cases_on `q = x` THEN1 (STRIP_TAC THEN EVAL_TAC THEN DECIDE_TAC) THEN
STRIP_TAC THEN
EVAL_TAC THEN
Q.PAT_ASSUM `! n x . naive_colouring_aux cs (n + 1) x <> n` (ASSUME_TAC o
Q.SPECL [`n+1`,`x`]) THEN
cheat) (* TODO *)

(* This next goal is the main missing part of the proof:
``
! n cs q.
(colouring_satisfactory (naive_colouring_aux cs (n+1)) cs)
==>
(colouring_satisfactory ((q += n) (naive_colouring_aux cs (n+1))) cs)
``
*)

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
!cs n . colouring_satisfactory (naive_colouring_aux cs n) cs
``,
Induct_on `cs` THEN1 (EVAL_TAC THEN DECIDE_TAC) THEN
Cases_on `h` THEN
EVAL_TAC THEN
STRIP_TAC THEN
STRIP_TAC THEN1 (
`colouring_satisfactory (naive_colouring_aux cs (n + 1)) cs` by METIS_TAC []
THEN
`~(MEM q r)` by cheat (* use the fact that the edge list is well-formed *)
(* need to add this to the assumptions of the overall goal *)
THEN
(* Now use the fact that naive colouring only assigns values upwards from n+1
This is the attempted proof above *)
`!x . (naive_colouring_aux cs (n + 1)) x <> n` by cheat THEN
FULL_SIMP_TAC std_ss [colouring_map_with_unused_update] THEN
METIS_TAC [map_doesnt_contain_unused_values])
THEN
(* Remaining goal seems like a possible lemma - giving a register a value which
is unused by any other should preserve colouring_satisfactory? *)
cheat)


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


val test = EVAL ``let cs = [(1, [2; 3]); (2, [1]); (3, [1])] in
colouring_satisfactory (naive_colouring cs) cs``


(* Determines whether a heuristic is acceptable
(*An acceptable heuristic only re-orders the input constraints *)
val heuristic_ok_def = Define `
    (heuristic_ok f 
`*)