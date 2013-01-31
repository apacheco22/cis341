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
let (%@) a b = (Int32.rem a b) 



let print32 (s: string) (i: int32) : unit = print_string (s ^ ": "); print_endline (Int32.to_string i) 
let print32_hex (s: string) (i:int32) : unit = Printf.printf ("%s: %lx \n") s i
let print_bool (s: string) (b:bool) : unit = Printf.printf ("%s: %b \n") s b
let print64 (s: string) (i: Int64.t) : unit = print_string (s ^ ": "); print_endline (Int64.to_string i) 

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
  xs.s_reg.(espi) <- mem_top;	xs 

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

let rec calc_addr (ia: ind) (regs: int32 array) (xs: x86_state) : int32 =
	let base = 
		match (ia.i_base) with
		| (Some x) -> get_reg_value x regs
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
						(*let ans = base +@ iscl +@ disp in print32 "offset" ans; ans*)
						base +@ iscl +@ disp

(*This one gives you the VALUE. mem[ind], reg[r]*)
let rec parse_operand (xs: x86_state) (op: opnd) : int32 =
	begin match op with
	| Imm x -> get_imm op
	(*| Lbl l -> Int32.of_int (find_insn l code) *)
	| Reg r -> get_reg_value r xs.s_reg
	| Ind i -> xs.s_mem.(map_addr(calc_addr i xs.s_reg xs))
	| _ -> print_endline "error in PO"; raise (X86_segmentation_fault "Invalid operand")
	end
	
let reg_of_op (op: opnd) : int =
	begin match op with
	| Reg r -> get_register_id r
	| _ -> raise (X86_segmentation_fault "Invalid register")
  end

let label_of_op (op: opnd) : lbl = 
	begin match op with
		| Lbl l -> l
		| _ -> raise (X86_segmentation_fault "Invalid label operand")
	end


let check_OF_64 (same: Int64.t * Int64.t) (diff: int32 * Int64.t) : bool =
	let s1 = fst same <@@ Int64.zero in
	let s2 = snd same <@@ Int64.zero in
	let d1 = Int64.of_int32 (fst diff) <@@ Int64.zero in
	let d2 = snd diff <@@ Int64.zero in
	if (s1 = s2) && (d1 <> d2) then true else false

let reset_flags (xs: x86_state) : unit = 
	xs.s_OF <- false;
	xs.s_ZF <- false;
	xs.s_SF <- false
	
let check_SZ (xs: x86_state) (num: int32) : unit = 
	if num = Int32.zero then xs.s_ZF <- true else xs.s_ZF <- false; 
	let msb = get_bit 31 num in
	xs.s_SF <- msb
	
let interpret_dest_no_cc (d: opnd) (s: int32) (xs: x86_state) : unit =
	begin match d with
		| Reg r -> xs.s_reg.(reg_of_op(d)) <- s 
		| Ind i -> xs.s_mem.(map_addr(calc_addr i xs.s_reg xs)) <- s
		| _ -> raise (X86_segmentation_fault "invalid destination operand")
	end		
	
let interpret_dest (d: opnd) (s: int32) (xs: x86_state) : unit =
	begin match d with
		| Reg r -> xs.s_reg.(reg_of_op(d)) <- s; check_SZ xs xs.s_reg.(reg_of_op(d)); 
		| Ind i -> xs.s_mem.(map_addr(calc_addr i xs.s_reg xs)) <- s; check_SZ xs xs.s_mem.(map_addr(calc_addr i xs.s_reg xs))
		| _ -> raise (X86_segmentation_fault "invalid destination operand")
	end	
	
let i64_insn (i: insn) (src_val32: int32) (d: opnd) (xs: x86_state) : unit =
		let src_val = Int64.of_int32(src_val32) in
			let dest_val = Int64.of_int32(parse_operand xs d) in			
			begin match i with
			| Add _ -> let s = Int64.to_int32(Int64.add dest_val src_val) in 
								 interpret_dest d s xs;
								 xs.s_OF <- check_OF_64 (dest_val,src_val) (s, src_val);
			| Sub _ -> let s = Int64.to_int32(Int64.add dest_val (Int64.neg(src_val))) in
								 interpret_dest d s xs;
								 xs.s_OF <- (check_OF_64 (dest_val, Int64.neg(src_val)) (s, Int64.neg(src_val)) 
															|| (src_val32=Int32.min_int));						
			| Imul _ -> let s64 = (Int64.mul dest_val src_val) in
									let	s = Int64.to_int32 s64 in
									interpret_dest d s xs;
									if (Int64.compare s64 (Int64.of_int32(Int32.max_int))) <= 0 
										then xs.s_OF <- false else xs.s_OF <- true; 
			| _ -> ();
		 end
		
let shift_insn (i: insn) (dest: opnd) (amt: opnd) (xs: x86_state) : unit = 
	let num_bits = match amt with
		| Imm i -> parse_operand xs amt
		| ecx -> parse_operand xs amt
		in let dest_val = parse_operand xs dest in 
			let shifted_val = match i with
				| Sar _ -> 	if num_bits = 1l then xs.s_OF <- false else (); 
										Int32.shift_right dest_val (Int32.to_int(num_bits)) 
				| Shl _ ->  if (((get_bit 31 dest_val) <> (get_bit 30 dest_val)) && num_bits = 1l) 
										then xs.s_OF <- true else (); 
										Int32.shift_left dest_val (Int32.to_int(num_bits))
				| Shr _ -> if (num_bits = 1l) then 
											xs.s_OF <- get_bit 31 dest_val else ();
										Int32.shift_right_logical dest_val (Int32.to_int(num_bits))
				| _ -> 0l
				in interpret_dest dest shifted_val xs;
				if num_bits <> 0l then check_SZ xs shifted_val else ()
				
let parse_insn (i: insn) (xs: x86_state) : unit = 
	begin match i with
	| Neg d -> let num = parse_operand xs d in
						 if (num <=@ Int32.min_int) then (xs.s_OF <- true) else ();
						 let negated = (Int32.lognot num) +@ 0x00000001l in
						 interpret_dest d negated xs;
	| Add (dest, src) -> let sval = parse_operand xs src in
											 i64_insn i sval dest xs;
	| Sub (dest, src) -> let sval = parse_operand xs src in
											 i64_insn i sval dest xs;
	| Imul (rg, src) -> let sval = parse_operand xs src in
											 i64_insn i sval (Reg rg) xs;
	| Not dest -> 	let num = parse_operand xs dest in
			let negated = (Int32.lognot num) in
			interpret_dest dest negated xs;	
	| And (dest, src)-> 	let num = parse_operand xs dest in
				let sval = parse_operand xs src in
				let anded = Int32.logand sval num in
				interpret_dest dest anded xs; check_SZ xs anded; xs.s_OF <- false;
	| Or (dest, src) -> 	let num = parse_operand xs dest in
				let sval = parse_operand xs src in
				let anded = Int32.logor sval num in
				interpret_dest dest anded xs; check_SZ xs anded; xs.s_OF <- false;
	| Xor (dest, src) -> 	let num = parse_operand xs dest in
				let sval = parse_operand xs src in
				let anded = Int32.logxor sval num in
				interpret_dest dest anded xs; check_SZ xs anded; xs.s_OF <- false;
	| Sar (dest, amt) -> shift_insn i dest amt xs															
	| Shl (dest, amt) -> shift_insn i dest amt xs
	| Shr (dest, amt) -> shift_insn i dest amt xs
	| Setb (dest, cc) -> let dest_val = parse_operand xs dest in 
													if (condition_matches xs cc) then 
														(interpret_dest_no_cc dest (Int32.logor (Int32.logand dest_val 0xfff0l) 0x0001l) xs)
														  else (interpret_dest_no_cc dest (Int32.logor (Int32.logand dest_val 0xfff0l) 0x0000l) xs);
	| Lea (dest, ind) -> let addr = calc_addr ind xs.s_reg xs in
													xs.s_reg.(get_register_id dest) <- addr
	| Mov (dest, src) -> 
					let s = parse_operand xs src in
					interpret_dest_no_cc dest s xs		
	| Push src -> xs.s_reg.(espi) <- xs.s_reg.(espi) -@ 4l;
								xs.s_mem.(map_addr(xs.s_reg.(espi))) <- (parse_operand xs src);
	| Pop dest -> let popped = xs.s_mem.(map_addr(xs.s_reg.(espi))) in
									interpret_dest_no_cc dest popped xs;
									xs.s_reg.(espi) <- xs.s_reg.(espi) +@ 4l;
	| Cmp (src1, src2) ->
		
				let s1val = parse_operand xs src1 in
				let src1_val = Int64.of_int32(s1val) in				
				let s2val = parse_operand xs src2 in
				let src2_val = Int64.of_int32(s2val) in
				let s = Int64.to_int32(Int64.add src1_val (Int64.neg(src2_val))) in
								 xs.s_OF <- (check_OF_64 (src1_val, Int64.neg(src2_val)) (s, Int64.neg(src2_val)) 
															|| (s2val=Int32.min_int));
						let msb = get_bit 31 s in
						xs.s_SF <- msb;
	| J (cc, clbl) -> ();
	| Ret -> xs.s_reg.(espi) <- (xs.s_reg.(espi) +@ 4l)
	| _ -> raise (X86_segmentation_fault "invalid insn")
	end
		
	let rec 
		interpret (code: insn_block list) (xs: x86_state) (l: lbl) : unit =
			let index : int  = (find_insn l code) in
			let program = List.nth code index in				
					(*print_endline "Starting flags:";
					print_bool "OF" xs.s_OF;			
					print_bool "SF" xs.s_SF;
					print_bool "ZF" xs.s_ZF;*)
					run_block program.insns code xs;
					
					(*print_endline "Registers:";
					print32 "Eax" (get_reg_value Eax xs.s_reg);
					print32 "Ebx" (get_reg_value Ebx xs.s_reg);
					print32 "s_mem" xs.s_mem.(mem_size-1)*)
								
					(*print_endline "Ending flags:";
					print_bool "OF" xs.s_OF;			
					print_bool "SF" xs.s_SF;
					print_bool "ZF" xs.s_ZF;*)
					
	and
		run_block (prgm: insn list) (code: insn_block list) (xs: x86_state) : unit =	
			begin match prgm with
			| [] -> ();
			| (Call op)::tl -> 
												 let f = label_of_op op in 
												 parse_insn (Push (Imm 0l)) xs; 
												 interpret code xs f;
												 run_block tl code xs;
			| (Jmp op)::tl -> let f = label_of_op op in
												interpret code xs f;	
			| (J (cc,lbl))::tl -> if (condition_matches xs cc) then 
															interpret code xs lbl else
																run_block tl code xs;
			|	h::[] -> if h = Ret then parse_insn h xs else raise (X86_segmentation_fault "Block ended without return")												
			| h::tl -> parse_insn h xs; run_block tl code xs;
			end
			
let run (code:insn_block list) : int32 =
  let main = X86.mk_lbl_named "main" in
  let xs = mk_init_state () in
  let _ = interpret code xs main in
    xs.s_reg.(eaxi)
      
