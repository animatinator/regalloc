
(* -- THIS FILE --

  This file defines a small register-based language. We give it both a
  functional semantics and a relational big-step semantics.

  Why two semantics? It's conventional to define operational semantics
  as using inductive relations (RTL_rules below). However, for some
  purposes, it's nicer to define the semantics as a function.

  But will the functional formulation still work if a While construct
  is added to the language? Yes, using a clock, as in lectures, it can
  be made to work just as well as a relational definition. The nice
  thing about a functional semantics is that one can evaluate it using
  EVAL (see below).

  Is this language not overly simple? It's very simple, but it can be
  extended reasonably easily to include: a memory and Store/Load
  instructions; to parametrise the architecture size (i.e. replace
  word32 by n-bit words); to include a clock and non-termination; to
  have function calls and program context etc.

  Let's start with this simple language and extend it as necessary.

  This language represents register names as natural numbers. In other
  words, there are infinitely many register names. The aim of register
  allocation is to make sure that only registers 0..N (for some
  specified N) are used by Const and Binop. The Move instruction is
  there to allow spilled values of spilled registers to be moved in
  and out of these special 0..N registers.

*)


(* Standard boilerplate starts. *)

open HolKernel Parse boolLib bossLib lcsymtacs;

val _ = new_theory "rtl_lang";

open arithmeticTheory listTheory combinTheory pairTheory wordsTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory wordsLib;

(* Standard boilerplate ends. *)


(* -- SYNTAX -- *)

(* Register/variable names are modelled as numbers (type num). *)

(* The abstract syntax is defined as datatype using Hol_datatype.
   Note about syntax: here "=>" can be tought of as product, e.g.
   ``Eq 0 300w`` is valid according to "Eq of num => word32" *)

val _ = Hol_datatype `
  binop = Add | Sub | And | Or | Xor `

val _ = Hol_datatype `
  test = Eq of num => word32 `;

val _ = Hol_datatype `
  code =
    Skip
  | Const     of num => word32
  | Binop     of num => binop => num => num
  | Move      of num => num
  | Seq       of code => code
  | If        of test => code => code `

(* We overload ";;" with Seq and make it an infix. *)

val _ = set_fixity ";;" (Infixr 300);
val _ = overload_on (";;",``Seq``);

(* -- SEMANTICS -- *)

(* The state is mapping of type: num -> word32. *)

val eval_binop_def = Define `
  (eval_binop Add v w = v + w:word32) /\
  (eval_binop Sub v w = v - w) /\
  (eval_binop And v w = v && w) /\
  (eval_binop Or  v w = v || w) /\
  (eval_binop Xor v w = v ?? w)`;

val eval_test_def = Define `
  (eval_test s (Eq v c) = ((s: num -> word32) v = c))`;

(* functional semantics *)

val eval_code_def = Define `
  (eval_code Skip s = s) /\
  (eval_code (Const r v) s = (r =+ v) s) /\
  (eval_code (Move r1 r2) s = (r1 =+ (s r2)) s) /\
  (eval_code (Binop r1 b r2 r3) s = (r1 =+ eval_binop b (s r2) (s r3)) s) /\
  (eval_code (Seq c1 c2) s = eval_code c2 (eval_code c1 s)) /\
  (eval_code (If t c1 c2) s =
     eval_code (if eval_test s t then c1 else c2) s)`

(* relational big-step semantics *)

val (RTL_rules,RTL_ind,RTL_cases) = Hol_reln `
  (!s.
     RTL Skip s s) /\
  (!v n s.
     RTL (Const v n) s ((v =+ n) s)) /\
  (!v1 v2 s.
     RTL (Move v2 v1) s ((v2 =+ (s v1)) s)) /\
  (!v1 v2 v3 b s.
     RTL (Binop v3 b v1 v2) s ((v3 =+ eval_binop b (s v1) (s v2)) s)) /\
  (!c1 c2 s1 s2 s3.
     RTL c1 s1 s2 /\ RTL c2 s2 s3 ==>
     RTL (Seq c1 c2) s1 s3) /\
  (!t c1 c2 s1 s2.
     RTL (if eval_test s1 t then c1 else c2) s1 s2 ==>
     RTL (If t c1 c2) s1 s2)`


(* -- RANDOM PROOFS -- *)

(* relational and functional semantics are interchangeable *)

val RTL_eval_code = prove(
  ``!c s1 s2. RTL c s1 s2 <=> (s2 = eval_code c s1)``,
  Induct
  THEN SIMP_TAC std_ss [eval_code_def]
  THEN ONCE_REWRITE_TAC [RTL_cases]
  THEN SIMP_TAC (srw_ss()) []
  THEN METIS_TAC []);

(* assigned vars are the only ones that can change *)

val assigned_def = Define `
  (assigned Skip = {}) /\
  (assigned (Const r v) = {r}) /\
  (assigned (Move r r1) = {r}) /\
  (assigned (Binop r b r1 r2) = {r}) /\
  (assigned (Seq c1 c2) = assigned c1 UNION assigned c2) /\
  (assigned (If t c1 c2) = assigned c1 UNION assigned c2)`;

val assigned_eval_code = prove(
  ``!c s1 s2.
      (eval_code c s1 = s2) ==>
      !v. ~(v IN assigned c) ==> (s1 v = s2 v)``,
  Induct
  THEN FULL_SIMP_TAC std_ss [assigned_def,eval_code_def,APPLY_UPDATE_THM,
         NOT_IN_EMPTY,IN_INSERT]
  THEN METIS_TAC [IN_UNION]);

(* evaluating the semantics *)

val test = EVAL
  ``eval_code (Const 0 3w ;; Const 1 4w ;; Binop 2 Add 0 1)
              (\v. 0w)
              2``

val _ = export_theory();
