(* Clash graph data type tests *)


(* Defining types for registers, vertices, edges and sets thereof *)
val register_def = Hol_datatype `
    REGISTER = R of num
`

val vertex_list_def = Hol_datatype `
    VERTEX_LIST = VLIST of (REGISTER -> bool)
`

val edge_def = Hol_datatype `
    EDGE = E of REGISTER => REGISTER
`

val edge_list_def = Hol_datatype `
    EDGE_LIST = ELIST of (EDGE -> bool)
`

val clash_graph_def = Hol_datatype `
    CLASH_GRAPH = CG of VERTEX_LIST => EDGE_LIST
`


(* Simple functions for checking edge and vertex membership *)
val contains_vertex_def = Define `
    (contains_vertex v (CG (VLIST vlist) elist) =
    		     v IN vlist)
`

val contains_edge_def = Define `
    (contains_edge e (CG (VLIST vlist) (ELIST elist)) =
    		   e IN elist)
`


(* Functions for adding vertices and edges *)
val add_vertex_def = Define `
    (add_vertex v (CG (VLIST vlist) elist) =
    		(CG
			(VLIST (v INSERT vlist))
			elist
		)
    )
`

val add_edge_def = Define `
    (add_edge (R a) (R b) (CG (VLIST vlist) (ELIST elist)) =
    	      (CG
	      	  (VLIST vlist)
		  (ELIST ((E (R a) (R b)) INSERT
		  	 ((E (R b) (R a)) INSERT elist)))
	      )
    )
`


(* Some simple proofs *)

(* Adding vertices works *)
val add_vertex_works = prove(
``
contains_vertex v (add_vertex v graph)
``,
Induct_on `graph` THEN
Induct_on `V` THEN
RW_TAC bool_ss [add_vertex_def] THEN
EVAL_TAC)

(* Adding edges works *)
val add_edge_works = prove(
``
contains_edge (E (R a) (R b)) (add_edge (R a) (R b) graph) /\
contains_edge (E (R b) (R a)) (add_edge (R a) (R b) graph)
``,
Induct_on `graph` THENL [  (* Realised recently that these don't have to be THENL
				where there is only one subgoal, so this could be
				made neater *)
RW_TAC bool_ss [] THENL [
Induct_on `V` THENL [ (* should use Cases_on in these places *)
Induct_on `E'` THENL [
RW_TAC bool_ss [] THEN
RW_TAC bool_ss [add_edge_def] THEN
RW_TAC bool_ss [contains_edge_def] THEN
EVAL_TAC]],
Induct_on `V` THENL [
Induct_on `E'` THENL [
RW_TAC bool_ss [] THEN
RW_TAC bool_ss [add_edge_def] THEN
RW_TAC bool_ss [contains_edge_def] THEN
EVAL_TAC]]]])

(* Magnus version *)
val add_edge_works = prove(
  ``contains_edge (E (R a) (R b)) (add_edge (R a) (R b) graph) /\
    contains_edge (E (R b) (R a)) (add_edge (R a) (R b) graph)``,
  Cases_on `graph` THEN
  Cases_on `V` THEN
  Cases_on `E'` THEN
  EVAL_TAC);
