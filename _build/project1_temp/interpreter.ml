(* CIS341: Project 1 Interpreter *)
(* Author: Steve Zdancewic *)

open X86


(* Int32 / Int64 abbreviations and infix arithmetic *)
let (+@) = Int32.add
let (-@) = Int32.sub
let (/@) = Int32.div
let ( *@ ) = Int32.mul
let (<@) a b = (Int32.compare a b) < 0
let (<=@) a b = (Int32.compare a b) <= 0
let (>@) a b = (Int32.compare a b) > 0
let (>=@) a b = (Int32.compare a b) >= 0
let (<@@) a b = (Int64.compare a b) < 0
let (%@) a b = (Int32.rem a b) (*Allison's addition*)


exception X86_segmentation_fault of string

(* Interpret the registers as indices into the register file array *)
let eaxi = 0
let ebxi = 1
let ecxi = 2
let edxi = 3
let esii = 4
let edii = 5
let ebpi = 6
let espi = 7 

let get_register_id = function
  | Eax -> eaxi 
  | Ebx -> ebxi 
  | Ecx -> ecxi 
  | Edx -> edxi 
  | Esi -> esii 
  | Edi -> edii 
  | Ebp -> ebpi
  | Esp -> espi


let mem_size = 1024                 (* Size of memory in words *)
let mem_top : int32 = 0xfffffffcl   (* Last addressable memory location *)
let mem_bot : int32 =               (* First addressable memory location *)
	  (Int32.of_int (mem_size * 4)) *@ (-1l)

(* 
   Maps virtual addresses (int32 addresses) to physical addresses (int indices). 
   Raises an X86_segmentation_fault exception if the provided virtual address 
   does not map or if the address is unaligned. 
*)
let map_addr (addr:int32) : int =
	if ((addr %@ 4l <> 0l) || ( (<@) mem_top addr) || ( (>@) mem_bot addr)) 
	then raise (X86_segmentation_fault "Invalid address")
	else mem_size - Int32.to_int((addr /@ 4l) *@ -1l)


type x86_state = {
    s_mem : int32 array;    (* 1024 32-bit words -- the heap *)
    s_reg : int32 array;    (* 8 32-bit words -- the register file *)
    mutable s_OF : bool;    (* overflow flag *)
    mutable s_SF : bool;    (* sign bit flag *)
    mutable s_ZF : bool;    (* zero flag *)
}

let mk_init_state () : x86_state = 
  let xs = {
  s_mem = Array.make mem_size 0l;
  s_reg = Array.make 8 0l;
  s_OF  = false;
  s_SF  = false;
  s_ZF  = false;
  } in
  xs.s_reg.(espi) <- mem_top; xs 

let print_state (xs:x86_state) : unit =
  (Array.iter (fun e -> Printf.printf "%lx " e) xs.s_mem);
  (Printf.printf "\neax: %lx ebx: %lx ecx: %lx edx: %lx" xs.s_reg.(eaxi)
      xs.s_reg.(ebxi) xs.s_reg.(ecxi) xs.s_reg.(edxi));
  (Printf.printf "\nesi: %lx edi: %lx ebp: %lx esp: %lx" xs.s_reg.(esii)
      xs.s_reg.(edii) xs.s_reg.(ebpi) xs.s_reg.(espi));
  (Printf.printf "\nOF: %b SF: %b ZF: %b\n" xs.s_OF xs.s_SF xs.s_ZF)
  

(* Helper function that determines whether a given condition code
   applies in the x86 state xs. *)  
let condition_matches (xs:x86_state) (c:X86.cnd) : bool =
	begin match c with
	| Eq -> if xs.s_ZF = true then true else false
	| Zero -> if xs.s_ZF = true then true else false
	| NotEq -> if xs.s_ZF = true then false else true
	| NotZero -> if xs.s_ZF = true then false else true 
	| Slt -> if (xs.s_OF <> xs.s_SF) then true else false
	| Sge -> if (xs.s_OF = xs.s_SF) then true else false
	| Sle -> if ((xs.s_OF <> xs.s_SF) || xs.s_ZF = true) then true else false
	| Sgt -> if ((xs.s_OF <> xs.s_SF) || xs.s_ZF = true) then false else true
	end


(* Returns the bit at a given index in a 32-bit word as a boolean *)
let get_bit bitidx n =
  let shb = Int32.shift_left 1l bitidx in
  Int32.logand shb n = shb  

let get_imm (imm: opnd) : int32 =
	begin match imm with
	| Imm x -> x
	| _ -> raise (X86_segmentation_fault "Invalid immediate operand")
	end	
	
let find_insn (label: lbl) (code: insn_block list) : int =
	let count = ref 0 in
	let rec loop (tail: insn_block list) : int = 
		begin match tail with
		| [] -> raise (X86_segmentation_fault "Label not found")
		| h::tl -> if h.label = label then !count else (count := !count + 1; loop tl)
		end
	in loop code
	
let get_reg_value (r: reg) (s_reg: int32 array) : int32 = 
	Array.get s_reg (get_register_id r)
	
let calc_addr (ia: ind) (regs: int32 array) : int32 =
	let base = 
		match (ia.i_base) with
		| (Some x) -> Int32.of_int(get_register_id x)
		| _ -> 0l
		in
			let iscl =
				match (ia.i_iscl) with
				| Some (r,scl) -> (get_reg_value r regs) *@ scl
				| _ -> 0l
				in
					let disp = 
						match (ia.i_disp) with
						| Some(DLbl l) -> raise (X86_segmentation_fault "Cannot jump to indirect label")
						| Some(DImm x) -> x
						| _ -> 0l
						in
						base +@ iscl +@ disp
		
let parse_operand (code: insn_block list) (xs: x86_state) (op: opnd) : int32 =
	begin match op with
	| Imm x -> get_imm op
	| Lbl l -> Int32.of_int (find_insn l code)
	| Reg r -> get_reg_value r xs.s_reg
	| Ind i -> calc_addr i xs.s_reg
	end

let operand_label (op: opnd) : lbl = 
	begin match op with
		| Lbl l -> l
		| _ -> raise (X86_segmentation_fault "Invalid label operand")
	end

let push (o: opnd) : unit =
	print_endline "push"

let parse_insn (i: insn) : unit = 
	begin match i with
	| Neg d -> print_endline "neg"
	| Add (dest, src) -> print_endline "add"
	| Sub (dest, src) -> print_endline "sub"
	| Imul (rg, src) -> print_endline "imul"
	| Not dest -> print_endline "not"
	| And (dest, src)-> print_endline "and"
	| Or (dest, src) -> print_endline "or"
	| Xor (dest, src) -> print_endline "xor"
	| Sar (dest, amt) -> print_endline "sar"
	| Shl (dest, amt) -> print_endline "shl"
	| Shr (dest, amt) -> print_endline "shr"
	| Setb (dest, cc) -> print_endline "setb"
	| Lea (dest, ind) -> print_endline "lea"
	| Mov (dest, src) -> print_endline "move"
	| Push src -> push src
	| Pop dest -> print_endline "pop"
	| Cmp (src1, src2) -> print_endline "cmp"
	| Jmp src -> print_endline "jmp"
	| J (cc, clbl) -> print_endline "j"
	| _ -> raise (X86_segmentation_fault "invalid insn")
	end
		
let rec interpret (code: insn_block list) (xs: x86_state) (l: lbl) : unit =
	let rec 
		get_program (rl: int Stack.t) (rb: int Stack.t) (code: insn_block list) (xs: x86_state) (l:lbl) : unit =		
			let index : int  = (find_insn l code) in
				Stack.push 0 rl;
				Stack.push index rb;
				let program = List.nth code index in				
					run_block rl rb program.insns code xs
	and
		run_block (rl: int Stack.t) (rb: int Stack.t) (prgm: insn list) (code: insn_block list) (xs: x86_state) : unit =	
			let line = ref (Stack.pop rl) in 
				let rec loop (prgm: insn list) : unit = 
					begin match prgm with
						| h::tl -> begin match h with
							| Call s -> print_endline "***CALL***";
												line := !line + 1;
												let src = operand_label s in 
												push (Imm 0l); 
												Stack.push (!line) rl;
												get_program rl rb code xs src 
				 			| Ret -> print_endline "ret!"; 
												let _ = Stack.pop rb in
													if (Stack.is_empty) rb then () else
													let rblock = (Stack.pop rb) in
														run_block rl rb (List.nth code rblock).insns code xs									
							| _ ->	parse_insn h; line := !line + 1; loop tl 
						end
					| [] -> raise (X86_segmentation_fault "Program finished without return statement")		
				end 
		in loop prgm
	in let rl = Stack.create () in let rb = Stack.create () in
	get_program rl rb code xs l  
		
let run (code:insn_block list) : int32 =
  let main = X86.mk_lbl_named "main" in
  let xs = mk_init_state () in
  let _ = interpret code xs main in
    xs.s_reg.(eaxi)
      
