(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x -> match x with
| Eq -> fz
| Neq -> not fz
| Gt -> (fs = fo) && not fz
| Lt -> ((fs && not fo) || (not fs && fo))
| Ge -> fs = fo
| Le -> (fs <> fo) || fz


(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  let addr_space = addr < mem_top && addr >= mem_bot in
  if addr_space then Some(Int64.to_int(Int64.sub addr mem_bot))
  else None

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

(* Stuff for step func *)
let range_check (num:int64) : int =
  match map_addr num with
  | None -> raise X86lite_segfault
  | Some a -> a
  
  let get_range (addr:int64) (m:mach) : int64 =
    let data = int64_of_sbytes [m.mem.(range_check addr); m.mem.(range_check (Int64.add addr 1L));
    m.mem.(range_check (Int64.add addr 2L)); 
    m.mem.(range_check (Int64.add addr 3L));
    m.mem.(range_check (Int64.add addr 4L)); 
    m.mem.(range_check (Int64.add addr 5L));
    m.mem.(range_check (Int64.add addr 6L)); 
    m.mem.(range_check (Int64.add addr 7L))]
    in data
  
  (* Interprets Operands *)
  let interp_op (m:mach) (op_list:operand list) (num:int) : int64 = 
  (* Use List.nth to get nth element of list for dest and src *)
  let op = List.nth op_list num in
  match op with
  | Imm i -> 
    begin
    (* Get i as a quad somehow *)
    match i with
    | Lit i -> i
    | Lbl i -> failwith "interp_op shouldn't be here1"
    end
  | Reg reg -> m.regs.(rind reg)
  | Ind1 i ->
    let data = 
    begin
    match i with
    | Lit i -> i
    | Lbl i -> failwith "interp_op shouldn't be here2"
    end
    in get_range data m
  | Ind2 reg -> let data = m.regs.(rind reg) in get_range data m
  | Ind3 (i, reg) -> 
    let data = 
    begin
      match i with
      | Lit i -> Int64.add i m.regs.(rind reg)
      | Lbl i -> failwith "interp_op shouldn't be here3"
    end
    in get_range data m
  
  let set_flags (m:mach) (flag:Int64_overflow.t) : unit =
    m.flags.fo <- flag.Int64_overflow.overflow;
    (* set if value is 0 *)
    m.flags.fz <- flag.Int64_overflow.value = 0L;
    (* Shift to get MSB, set if equal to 1 *)
    m.flags.fs <- (Int64.shift_right_logical flag.Int64_overflow.value 63) = 1L
  
  let set_value (m:mach) (op_list:operand list) (num:int) (data:int64) : unit =
    let op = List.nth op_list num in
    let data_to_set = Array.of_list (sbytes_of_int64 data) in
    let length = Array.length data_to_set in
    match op with
    | Reg reg -> m.regs.(rind reg) <- data
    | Ind1 ind1 ->
      let immop = 
        begin
        match ind1 with
        | Lit i -> i
        | Lbl i -> failwith "set_value shouldn't be here1"
        end
        in 
      let index = range_check immop in
      Array.blit data_to_set 0 m.mem index length
    | Ind2 ind2 -> let index = range_check m.regs.(rind ind2) in 
      Array.blit data_to_set 0 m.mem index length
    | Ind3 (ind3, reg) -> 
      let immop = 
        begin
          match ind3 with
          | Lit i -> Int64.add i m.regs.(rind reg)
          | Lbl i -> failwith "set_value shouldn't be here2"
        end
        in 
      let index = range_check immop in
      Array.blit data_to_set 0 m.mem index length
    | _ -> failwith "set_value should not be here3"
  
  let arithmetic (m:mach) (instr:ins) : unit = 
  let opcode, operator_list = instr in
  match opcode with
  | Negq -> 
    let dest = interp_op m operator_list 0 in 
    let value = Int64_overflow.neg dest in
      set_value m operator_list 0 value.Int64_overflow.value;
      set_flags m value;
      if dest = Int64.min_int then m.flags.fo <- true
  | Addq -> 
    let src = interp_op m operator_list 0 in 
    let dest = interp_op m operator_list 1 in
    let value = Int64_overflow.add dest src in
      set_value m operator_list 1 value.Int64_overflow.value;
      set_flags m value
  | Subq ->   
    let src = interp_op m operator_list 0 in 
    let dest = interp_op m operator_list 1 in
    let value = Int64_overflow.sub dest src in
      set_value m operator_list 1 value.Int64_overflow.value;
      set_flags m value;
      if src = Int64.min_int then m.flags.fo <- true
  | Imulq ->
    let src = interp_op m operator_list 0 in 
    let reg = interp_op m operator_list 1 in
    let value = Int64_overflow.mul reg src in
      set_value m operator_list 1 value.Int64_overflow.value;
      set_flags m value
  | Incq -> 
    let dest = interp_op m operator_list 0 in 
      set_value m operator_list 1 (Int64_overflow.succ dest).Int64_overflow.value;
      set_flags m (Int64_overflow.succ dest)
  | Decq ->
    let dest = interp_op m operator_list 0 in 
      set_value m operator_list 1 (Int64_overflow.pred dest).Int64_overflow.value;
      set_flags m (Int64_overflow.pred dest);
      if dest = Int64.min_int then m.flags.fo <- true
  | _ -> failwith "arithmetic should not be here"
  
  let logic (m:mach) (instr:ins) : unit = 
  let opcode, operator_list = instr in
  match opcode with
  | Notq -> 
    let dest = interp_op m operator_list 0 in 
      set_value m operator_list 0 (Int64.lognot dest)
  | Andq ->
    let src = interp_op m operator_list 0 in 
    let dest = interp_op m operator_list 1 in 
    let aand = Int64.logand dest src in
      set_value m operator_list 1 aand;
      set_flags m (Int64_overflow.ok aand)
  | Orq ->
    let src = interp_op m operator_list 0 in 
    let dest = interp_op m operator_list 1 in 
    let oor = Int64.logor dest src in
      set_value m operator_list 1 oor;
      set_flags m (Int64_overflow.ok oor)
  | Xorq ->
    let src = interp_op m operator_list 0 in 
    let dest = interp_op m operator_list 1 in 
    let xor = Int64.logor dest src in
      set_value m operator_list 1 xor;
      set_flags m (Int64_overflow.ok xor)
  | _ -> failwith "logic should not be here"
  
  let msb2_check (dest:int64) : bool =
    (* Get top 2 bits and check if equal*)
    Int64.shift_right_logical dest 63 = Int64.logand (Int64.shift_right_logical dest 62) 1L
  
  let change_byte (m:mach) (op_list:operand list) (num:int) (data:int64) : unit =
  let op = List.nth op_list num in
  match op with
  | Reg reg -> m.regs.(rind reg) <- data
  | Ind1 ind1 ->
    let immop = 
    begin
    match ind1 with
    | Lit i -> i
    | Lbl i -> failwith "change_byte shouldn't be here1"
    end
    in 
    let index = range_check immop in
    let bytes : sbyte list = sbytes_of_int64 data
    in m.mem.(index) <- List.nth bytes 0
  | Ind2 ind2 -> let index = range_check m.regs.(rind ind2) in 
    let bytes : sbyte list = sbytes_of_int64 data
    in m.mem.(index) <- List.nth bytes 0
  | Ind3 (ind3, reg) -> 
    let immop = 
    begin
    match ind3 with
    | Lit i -> Int64.add i m.regs.(rind reg)
    | Lbl i -> failwith "change_byte shouldn't be here2"
    end
    in
    let index = range_check immop in
    let bytes : sbyte list = sbytes_of_int64 data
    in m.mem.(index) <- List.nth bytes 0
  | _ -> failwith "change_byte should not be here3"
  
  let bit_manip (m:mach) (instr:ins) : unit = 
  let opcode, operator_list = instr in
  match opcode with
  | Sarq -> 
    let amt = interp_op m operator_list 0 in
    let dest = interp_op m operator_list 1 in
    let shift = Int64.shift_right dest (Int64.to_int amt) in
      set_value m operator_list 1 shift;
      if (Int64.to_int amt) <> 0 then set_flags m (Int64_overflow.ok shift);
      if (Int64.to_int amt) = 1 then m.flags.fo <- false
  | Shlq -> 
    let amt = interp_op m operator_list 0 in
    let dest = interp_op m operator_list 1 in
    let shift = Int64.shift_left dest (Int64.to_int amt) in
      set_value m operator_list 1 shift;
      if (Int64.to_int amt) <> 0 then set_flags m (Int64_overflow.ok shift);
      if (Int64.to_int amt) = 1 then 
        if msb2_check dest then m.flags.fo <- false 
        else m.flags.fo <- true
  | Shrq -> 
    let amt = interp_op m operator_list 0 in
    let dest = interp_op m operator_list 1 in
    let shift = Int64.shift_right_logical dest (Int64.to_int amt) in
      set_value m operator_list 1 shift;
      if (Int64.to_int amt) <> 0 then set_flags m (Int64_overflow.ok shift);
      if (Int64.to_int amt) = 1 then
        if Int64.shift_right_logical dest 63 = 1L then m.flags.fo <- true
        else m.flags.fo <- false
  | Set s -> 
    if interp_cnd m.flags s then change_byte m operator_list 0 1L
    else change_byte m operator_list 0 0L (* change to change last byte only *)
  | _ -> failwith "bit_manip should not be here"
  
  let data_mov (m:mach) (instr:ins) : unit = 
  let opcode, operator_list = instr in
  match opcode with
  | Leaq -> let ind = interp_op m operator_list 0 in
    set_value m operator_list 1 ind;
  | Movq -> let src = interp_op m operator_list 0 in 
    set_value m operator_list 1 src;
  | Pushq -> 
    let src = interp_op m operator_list 0 in 
      m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) ins_size;
      (* Use Ind2 to address Rsp *)
      set_value m [Ind2 Rsp] 0 src
  | Popq ->
    let dest = interp_op m [Ind2 Rsp] 0 in 
      set_value m operator_list 0 dest;
      m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) ins_size
  | _ -> failwith "data_mov should not be here"
  
  let control_flow (m:mach) (instr:ins) : unit = 
  let opcode, operator_list = instr in
  match opcode with
  | Cmpq -> 
    let src1 = interp_op m operator_list 0 in 
    let src2 = interp_op m operator_list 1 in 
    let value = Int64_overflow.sub src2 src1 in
      set_flags m value;
      if src1 = Int64.min_int then m.flags.fo <- true
  | Jmp -> let src = interp_op m operator_list 0 in m.regs.(rind Rip) <- src
      | Callq ->
        m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size;
        let src = interp_op m [Reg Rip] 0 in 
          m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
          (* Use Ind2 to address Rsp *)
          set_value m [Ind2 Rsp] 0 src;
        (* jump to given location *)
        let call_loc = interp_op m operator_list 0 in m.regs.(rind Rip) <- call_loc
  | Retq -> 
    let dest = interp_op m [Ind2 Rsp] 0 in 
      set_value m [Reg Rip] 0 dest;
      m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) ins_size
  | J j -> 
    let src = interp_op m operator_list 0 in
      if interp_cnd m.flags j then
      m.regs.(rind Rip) <- src
      else m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size
  | _ -> failwith "control_flow should not be here"
  
  let choose_instruction (m:mach) (instr:ins) : unit = 
  let opcode, operator_list = instr in
  match opcode with 
  | Negq | Addq | Subq | Imulq | Incq | Decq -> arithmetic m instr; 
    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size
  | Notq | Andq | Orq | Xorq -> logic m instr;
    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size
  | Sarq | Shlq | Shrq -> bit_manip m instr;
    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size
  | Set s -> bit_manip m instr;
    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size
  | Leaq | Movq | Pushq | Popq -> data_mov m instr;
    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size;
  | Cmpq -> control_flow m instr;
    m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size;
  | Jmp -> control_flow m instr
  | Callq -> control_flow m instr
  | Retq -> control_flow m instr
  | J j -> control_flow m instr

let read_first_byte (m:mach) (b:sbyte) : unit = 
match b with
| InsB0 instr -> choose_instruction m instr
(* If InsFrag, need to move until InsB0 *)
| InsFrag -> m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 1L
| Byte dontcare -> ()
  
let step (m:mach) : unit =
let get_instr = m.regs.(rind Rip) in
let check_range = map_addr get_instr in
let addr = 
  match check_range with
  | None -> raise X86lite_segfault
  | Some a -> a
  in read_first_byte m m.mem.(addr)

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)

 (* Note
    Need text size to get data position so need to get sizes first
  *)

  type map = (lbl * quad) list
  let data_size_helper (s:int64) (d:data) : int64 = 
    begin match d with
    | Asciz a -> 
      let len = Int64.of_int (String.length a) in
      Int64.add s (Int64.add 1L len)
    | Quad q -> 
      begin match q with
      | Lit l -> Int64.add s 8L
      | Lbl l -> 
        let len = Int64.of_int (String.length l) in 
        Int64.add len (Int64.add s 1L) 
      end
    end
  
  
  let compute_size (s:(int64 * int64)) (e:elem) : (int64 * int64) =
    let size_t, size_d = s in
    begin match e.asm with
    | Text t -> 
      let list_size = (Int64.of_int (List.length t)) in
      (Int64.add size_t (Int64.mul list_size 8L), size_d)
    | Data d -> (size_t, Int64.add size_d (List.fold_left data_size_helper 0L d))
    end
  
  
  let rec map_contains (m:map) (k:lbl) : bool =
    begin match m with
    | (x, y)::tl -> 
      if x = k then true else map_contains tl k
    | [] -> false
    end
  
  let rec map_lookup (m:map) (k:lbl) : quad =
    begin match m with
    | (x, y)::tl -> 
      if x = k then y else map_lookup tl k
    | [] -> raise (Undefined_sym k)
    end
  
  
  let resolve_lbl_helper (m:map) (i:imm) : quad =
    begin match i with
    | Lit l -> l 
    | Lbl l -> Int64.add mem_bot (map_lookup m l)
    end
  
  let resolve_lbl (m:map * operand list) (o:operand) : (map * operand list) = 
    let _map, oper_l = m in
    begin match o with
    | Ind1 x -> (_map, oper_l @ [Ind1 (Lit (resolve_lbl_helper _map x))])
    | Ind3 (x,r) -> (_map, oper_l @ [Ind3 (Lit (resolve_lbl_helper _map x), r)])
    | Imm x -> (_map, oper_l @ [Imm (Lit (resolve_lbl_helper _map x))])
    | Reg r -> (_map, oper_l @ [Reg r])
    | Ind2 i -> (_map, oper_l @ [Ind2 i])
    end
  
  let patch_ins (m:map * sbyte list) (i:ins) : (map * sbyte list) =
    (* _map = same symbol table; sbyte_l = accumlated sbyte list*)
    let _map, sbyte_l = m in 
    let op, opr_l = i in
    let _, patched_opr_l = List.fold_left resolve_lbl (_map, []) opr_l in
    (_map, sbyte_l @ sbytes_of_ins (op, patched_opr_l))
  
  
  (* 
      takes in symbol_map dictionary, sbyte list
      match asm on text
      replace lbls according to map, update sbyte list
      if lbl not in map, exception
  
      return sbyte list
    *)  
  let handle_text (m:map * sbyte list) (e:elem) : (map * sbyte list) =
    let _map, text_seg = m in
    begin match e.asm with
    (* fold on map, t with patch_ins*)
    | Text t -> 
      let new_new_map, patched_ins = List.fold_left patch_ins (_map, text_seg) t in
      (new_new_map, patched_ins)
    | _ -> m
    end
  
  
  
  let handle_text_seg_labels (m:map * int64) (e:elem) : (map * int64) =
    let _map, list_size = m in
    begin match e.asm with
    (* fold on map, t with patch_ins*)
    | Text t -> 
      let label = e.lbl in 
      let new_map = 
        if not (map_contains _map label) then 
          _map @ [(label, list_size)]
        else
          raise (Redefined_sym label) in
      (new_map, Int64.add list_size (Int64.mul (Int64.of_int (List.length t)) 8L))
    | _ -> m
    end
  
  let data_helper (l:sbyte list) (d:data): sbyte list =
    l @ (sbytes_of_data d)
  
  (* 
    takes in symbol_map dictionary, sbyte list
    match asm on data
    update map, sbyte list
    
    return map, sbyte list
  *)
  let handle_data (t:int64 * map * sbyte list) 
                  (e:elem) : (int64 * map * sbyte list) = 
    begin match e.asm with
      | Data d -> 
        let size_text, _map, data_seg = t in
        let label = e.lbl in
        let new_map = 
          if not (map_contains _map label) then 
          (* update map *)
            let list_size = Int64.of_int (List.length data_seg) in
            _map @ [(label, (Int64.add size_text list_size))]
          else
            raise (Redefined_sym label) in
        let new_data_seg = List.fold_left data_helper data_seg d in
        (size_text, new_map, new_data_seg)
      | _ -> t
    end
  (* first generates map and data segment *)
  (* then folds on the program to generate text segment *)
  (* return text_seg, data_seg *)
  let resolve_symbols (p:prog) (s:int64) : (quad * sbyte list * sbyte list) =
    let size_text = s in
    let _, _map, data_seg = List.fold_left handle_data (size_text, [], []) p in
    let new_map, t = List.fold_left handle_text_seg_labels (_map, 0L) p in
    let _, text_seg = List.fold_left handle_text (new_map, []) p in
    ((resolve_lbl_helper new_map (Lbl "main")), text_seg, data_seg)
  
  (* Convert an X86 program into an object file:
     - separate the text and data segments
     - compute the size of each segment
        Note: the size of an Asciz string section is (1 + the string length)
  
     - resolve the labels to concrete addresses and 'patch' the instructions to 
       replace Lbl values with the corresponding Imm values.
  
     - the text segment starts at the lowest address
     - the data segment starts after the text segment
  
    HINT: List.fold_left and List.fold_right are your friends.
   *)
  let assemble (p:prog) : exec =
    let size_text, size_data = List.fold_left compute_size (0L, 0L) p in
    let main, text_seg, data_seg = resolve_symbols p size_text in
      {entry=main; text_pos=mem_bot; 
      data_pos=Int64.add mem_bot size_text;
      text_seg=text_seg; data_seg=data_seg}
  
  
  (* Convert an object file into an executable machine state. 
      - allocate the mem array
      - set up the memory state by writing the symbolic bytes to the 
        appropriate locations 
      - create the inital register state
        - initialize rip to the entry point address
        - initializes rsp to the last word in memory 
        - the other registers are initialized to 0
      - the condition code flags start as 'false'
  
    Hint: The Array.make, Array.blit, and Array.of_list library functions 
    may be of use.
  *)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
let cc_flags = {fo=false; fs=false; fz=false} in
let regs = Array.make nregs 0L in
(*Concat text and data *)
let sections = Array.of_list (text_seg @ data_seg) in
(* Hopefully manually setting bytes to 0 is ok *)
let mem_array = Array.make mem_size (Byte '\x00') in
let exit = Array.of_list (sbytes_of_int64 exit_addr) in
  (* Replace start with sections *)
  Array.blit sections 0 mem_array 0 (Array.length sections);
  (* Replace end with exit_addr *)
  Array.blit exit 0 mem_array (Int.sub mem_size 8) (Array.length exit);
  regs.(rind Rip) <- entry;
  (* initializes rsp to the last word in memory, 8 bytes=word?*)
  regs.(rind Rsp) <- Int64.sub mem_top 8L;
  {mem=mem_array; regs=regs; flags=cc_flags}
