(* A (virtual) register *)
val register_def = Hol_datatype `
    REGISTER = R of num
`

(* An instruction in the program *)
val instruction_def = Hol_datatype `
    INSTRUCTION = THREEVAL of REGISTER => REGISTER => REGISTER
`

(* A piece of code (sequence of instructions) *)
val code_def = Hol_datatype `
    CODE = INSTR of INSTRUCTION => CODE | TERMINATOR of INSTRUCTION
`


(* Get the set of registers an instruction uses *)
val get_instr_registers_def = Define `
    (get_instr_registers (THREEVAL (R r1) (R r2) (R r3)) = {r1;r2;r3})
`

(* Get the set of registers a piece of code uses *)
val get_code_registers_def = Define `
    (get_code_registers (INSTR instruction code) = get_instr_registers(instruction) UNION get_code_registers(code)) /\
    (get_code_registers (TERMINATOR instruction) = get_instr_registers(instruction))
`


(* Get the sources for a three-valued instruction *)
val get_sources_def = Define `
    (get_sources (THREEVAL _ (R s1) (R s2)) = {s1; s2})
`

(* Get the instruction's destination *)
val get_dest_def = Define `
    (get_dest (THREEVAL (R dest) _ _) = dest)
`


(* Get the set of variables live at a particular instruction *)
val get_live_variables_def = Define `
    (get_live_variables (TERMINATOR instruction) = get_sources instruction)
/\  (get_live_variables (INSTR instruction code) =
    	let live_after = get_live_variables code
	in
		(live_after DELETE (get_dest instruction))
		UNION (get_sources instruction)
    )
`

(* Prove that the returned set of live variables corresponds to the set formula
for variable liveness *)
val get_live_variables_correctness = prove(
``
(get_live_variables code = live_set) ==>
(get_live_variables (INSTR instruction code) =
		   (live_set DELETE (get_dest instruction))
		   UNION (get_sources instruction))
``,
	STRIP_TAC THEN RW_TAC bool_ss [get_live_variables_def])


(* Function to extract the set of instructions at which a variable is live *)
val get_live_range_def = Define `
    (get_live_range (R n) (TERMINATOR instruction) =
        if (n IN get_live_variables (TERMINATOR instruction)) then {instruction}
	else {}
    )
/\
    (get_live_range (R n) (INSTR instruction code) =
        if (n IN get_live_variables (INSTR instruction code)) then
	    instruction INSERT (get_live_range (R n) code)
	else
	    get_live_range (R n) code
		
    )
`

(* Now prove that the results from get_live_range are as expected according to get_live_variables *)
val get_live_range_contains_all = prove(
``
n IN get_live_variables (INSTR instruction code) ==>
instruction IN get_live_range (R n) (INSTR instruction code)
``,
STRIP_TAC THEN RW_TAC bool_ss [get_live_range_def] THEN EVAL_TAC)


val get_live_range_contains_no_spurious = prove(
``
instruction IN get_live_range (R n) (INSTR instruction code) ==>
(n IN get_live_variables (INSTR instruction code)
\/ instruction IN get_live_range (R n) (code))
``,
RW_TAC bool_ss [get_live_range_def])


(* Proving the same things for terminator instructions *)
val get_live_range_contains_all_terminator = prove(
``
n IN get_live_variables (TERMINATOR instruction) ==>
instruction IN get_live_range (R n) (TERMINATOR instruction)
``,
STRIP_TAC THEN RW_TAC bool_ss [get_live_range_def] THEN EVAL_TAC)

val get_live_range_contains_no_spurious_terminator = prove(
``
instruction IN get_live_range (R n) (TERMINATOR instruction) ==>
n IN get_live_variables (TERMINATOR instruction)
``,
RW_TAC bool_ss [get_live_range_def] THEN EVAL_TAC)