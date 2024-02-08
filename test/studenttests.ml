open Util.Assert
open X86
open Simulator
open Gradedtests
open Asm

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let mov_ri =
 test_machine
 [
 InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 ]

(*Euclid's Algorithm from EECS 376*)
let euclid_GCD x y = [ text "main"
                          [ Movq,  [~$x; ~%R08]
				  ; Movq,  [~$y; ~%R09]
				  ; Cmpq,  [~$0; ~%R08]
                          ; Cmpq,  [~$0; ~%R08]
                          ; J Eq,  [~$$"Exit"]
				  ; Cmpq,  [~$0; ~%R09]
                          ; J Eq,  [~$$"Exit"]
                          ; Jmp,   [~$$"Loop"]
                          ]			  
                    ; text "Loop"
                          [ Cmpq,  [~%R09; ~%R08]
                          ; J Eq,  [~$$"Move Return Value"]
				  ; J Lt,  [~$$"R9<R8"]
			        ; J Gt,  [~$$"R9>R8"]
				  ]
			  ; text "R9>R8"
                          [ Subq,  [~%R09; ~%R08] 
				  ;	Jmp,   [~$$"Loop"]
                          ]
			  ; text "R9<R8"
                          [ Subq,  [~%R08; ~%R09]
				  ;	Jmp,   [~$$"Loop"]
                          ]
			  ; text "Move Return Value"
				  [ Movq,  [~%R08; ~%Rax]
				  ; Jmp,   [~$$"Exit"]
				  ]
                    ; text "Exit"
                          [ Retq,  [] ]
]

let provided_tests : suite = [
  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
    ("egcd1", program_test (euclid_GCD (123) (15)) 3L);
    ("egcd2", program_test (euclid_GCD (257) (12)) 1L);
    ("egcd3", program_test (euclid_GCD (0) (12)) 0L);
    ("egcd4", program_test (euclid_GCD (17) (17)) 17L);
    ("egcd5", program_test (euclid_GCD (123) (98766)) 3L);]);
]