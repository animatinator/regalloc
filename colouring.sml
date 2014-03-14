open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory combinTheory pairTheory
     finite_mapTheory relationTheory optionTheory pred_setTheory;


val getConflicts_def = Define `
    (getConflicts [] live x y = ~(MEM x live) \/ ~(MEM y live)) /\
    (getConflicts ((Inst r0 r1 r2)::code) live x y =
		     (~(MEM x (get_live ((Inst r0 r1 r2)::code) live))
		     \/ ~(MEM y (get_live ((Inst r0 r1 r2)::code) live)))
		     /\ (getConflicts code live x y)
    )
`