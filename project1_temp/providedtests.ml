open Assert
open Interpreter
open X86

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let print32 (s: string) (i: int32) : unit = print_string (s ^ ": "); print_endline (Int32.to_string i) 
let print32_hex (s: string) (i:int32) : unit = Printf.printf ("%s: %lx \n") s i
let print_bool (s: string) (b:bool) : unit = Printf.printf ("%s: %b \n") s b
let print64 (s: string) (i: Int64.t) : unit = print_string (s ^ ": "); print_endline (Int64.to_string i) 


let st_test (s:string) (code:insn_block list) (f:x86_state -> bool) () =
  let st = mk_init_state () in
  let _ = interpret code st (mk_lbl_named "main") in
    if (f st) then () else failwith ("expected " ^ s)

let provided_tests : suite = [
	
  Test ("Student-Provided Big Test for Part II", 
		[("sar",
			st_test "sar ff00" 
      	[(mk_block "main" [
	  	Mov (eax, Imm 0xf0000000l);
	  	Sar (eax, Imm 4l);
			Ret;
		])] 
		(fun state -> print32_hex "reg state" state.s_reg.(0); print_bool "OF" state.s_OF; state.s_reg.(0) = 0xff000000l));  
	
	
		("shl",
			st_test "shl" 
      	[(mk_block "main" [
	  	Mov (eax, Imm 0x000000ffl);
	  	Shl (eax, Imm 8l);
			Ret;
		])] 
		(fun state -> print32_hex "reg state" state.s_reg.(0); print_bool "OF" state.s_OF; state.s_reg.(0) = 0x0000ff00l)); 
		
		("shl-cond",
			st_test "shl" 
      	[(mk_block "main" [
	  	Mov (eax, Imm 0x80000000l);
	  	Shl (eax, Imm 1l);
			Ret;
		])] 
		(fun state -> print_bool "OF" state.s_OF; state.s_OF = true));   
	
	("shr ",
			st_test "shr" 
      	[(mk_block "main" [
	  	Mov (eax, Imm 0xff00000l);
	  	Shr (eax, Imm 8l);
			Ret;
		])] 
		(fun state -> print32_hex "reg state" state.s_reg.(0); state.s_reg.(0) = 0xff000l));  
		
		
		("set_b",
			st_test "set_b" 
      	[(mk_block "main" [
	  	Mov (eax, Imm 0xfffdl);
			Add (eax, Imm 0x1l);
			Setb (eax, Zero);
			Ret;
		])] 
		(fun state -> print32_hex "reg state" state.s_reg.(0); state.s_reg.(0) = 0xfff0l));  
	
	("lea",
			st_test "lea" 
      	[(mk_block "main" [
			Lea (Eax, {i_base = None; i_iscl = None; i_disp = Some (DImm 7l)});
			Ret;
		])] 
		(fun state -> print32_hex "reg state" state.s_reg.(0); state.s_reg.(0) = 0x7l));  
	
	
	
	]
	
	
	)
]