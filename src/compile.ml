(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...

*)

open Format
open Ast
open Tast
open X86_64

exception Anomaly of string

let debug = ref false
let tvoid = Tmany []

let strings = Hashtbl.create 32 (*table label, string*)
let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s; 
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  exit_label: string;
  ofs_this: int;
  nb_locals: int ref; (* maximum *)
  mutable next_local: int; (* 0, 1, ... *)
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0 }

let mk_bool d = { expr_desc = d; expr_typ = Tbool }

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true ++
  movq (imm 0) (reg rdi) ++ jmp l_end ++
  label l_true ++ movq (imm 1) (reg rdi) ++ label l_end

let rec expr env e = match e.expr_desc with
  | TEskip ->
    nop

  | TEconstant (Cbool true) ->
    movq (imm 1) (reg rdi)

  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)

  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)

  | TEnil ->
    xorq (reg rdi) (reg rdi)

  | TEconstant (Cstring s) ->
    let labelstring = alloc_string s in 
      movq (ilab labelstring) (reg rdi) (*peut on avoir 2 string identique avec 2 label diff ?*)
  
  | TEbinop (Band, e1, e2) ->
    expr env (mk_bool(TEif (e1, e2, mk_bool (TEconstant (Cbool false)))))
    
  | TEbinop (Bor, e1, e2) ->
    expr env (mk_bool(TEif (e1, mk_bool (TEconstant (Cbool true)), e2)))
   
  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) ->
    expr env e1 ++ 
    pushq (reg rdi) ++ 
    expr env e2 ++ 
    popq (rax) ++ 
    cmpq (reg rdi) (reg rax) ++ compile_bool
   ( match op with 
    | Blt -> js (* normalement bon sens des registres, déjà vérifié *)
    | Ble -> jle 
    | Bgt -> jg
    | Bge -> jge
    | _ -> assert false)
    
  | TEbinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1, e2) ->
    expr env e1 ++ 
    pushq (reg rdi) ++ 
    expr env e2 ++ 
   ( match op with 
    | Badd -> movq (reg rdi) (reg rax) ++ 
              popq (rdi) ++ (*e1 dans rdi, e2 dans rax*)
              addq (reg rax) (reg rdi) 
    | Bsub -> movq (reg rdi) (reg rax) ++ 
              popq (rdi) ++
              subq (reg rax) (reg rdi)
    | Bmul -> movq (reg rdi) (reg rax) ++ 
              popq (rdi) ++ 
              imulq (reg rax) (reg rdi)
    | Bdiv -> popq (rax) ++ (*divise rax par l'entrée, mets dividende dans rax, reste dans rdx, ne pas oublier de mettre  rdx à 0*)
              xorq (reg rdx) (reg rdx) ++  (*e1 dans rax, e2 dans rdi*)
              idivq (reg rdi) ++ 
              movq (reg rax) (reg rdi)
    | Bmod -> popq (rax) ++ (*divise rax par l'entrée, mets dividende dans rax, reste dans rdx, ne pas oublier de mettre  rdx à 0*)
              xorq (reg rdx) (reg rdx) ++  (*e1 dans rax, e2 dans rdi*)
              idivq (reg rdi) ++ 
              movq (reg rdx) (reg rdi)
    | _ -> assert false)

  | TEbinop (Beq | Bne as op, e1, e2) -> (*attention, comparaison tout type !*)
    expr env e1 ++ 
    pushq (reg rdi) ++
    expr env e2 ++ 
    (match e1.expr_typ with 
      | Tint | Tbool -> (
        popq (rax) ++
        cmpq (reg rdi) (reg rax) ++
        compile_bool (match op with 
          | Beq -> je
          | Bne -> jne
          | _ -> assert false ))
      | Tstring -> assert false (*comment comparer des strings ? *)
      | Tstruct s -> assert false (*comparer champ par champ*)
      | _ -> assert false (*est ce qu'il faut faire le reste*)
      )

  | TEunop (Uneg, e1) ->
    expr env e1 ++ 
    negq (reg rdi) 

  | TEunop (Unot, e1) ->
    expr env e1 ++ 
    notq (reg rdi)

  | TEunop (Uamp, e1) ->
    (* TODO code pour & *) assert false 
  | TEunop (Ustar, e1) ->
      (expr env e1) ++ movq (ind rdi) (reg rdi)

  | TEprint el ->
    (match el with 
      | [] -> nop
      | x::q -> begin expr env x ++ 
        (match x.expr_typ with 
          | Tint | Tbool -> call "print_int"         
          | Tstring ->  call "print_string" 
          (*structures : imprimer les fields, transformer les fields en liste *)
          | _ -> nop) ++ (*faire les autres print : structures, pointeurs*)
        expr env ({expr_desc = TEprint q; expr_typ = tvoid})
      end)

  | TEident x -> movq (ind ~ofs:(x.v_addr) rbp) (reg rdi)
  | TEassign ([{expr_desc=TEident x}], [e1]) ->
    (* TODO code pour x := e *) assert false 
  | TEassign ([lv], [e1]) ->
    (* TODO code pour x1,... := e1,... *) assert false 
  | TEassign (_, _) ->
     assert false
  | TEblock el -> 
  begin
    let cur_env = ref env and nb_local = ref 0 in
    let block_processing env init e = match e with 
      | {expr_desc = TEvars (vl,el)} -> nb_local := !nb_local + (List.length vl); init ++ decl_var cur_env nop vl
      | h -> init ++ expr !cur_env h
    in
      let t1 = List.fold_left (block_processing !cur_env) nop el in
      let t2 = ref nop in
        for i=0 to !nb_local-1 
        do
          t2 := !t2 ++ popq rdi
        done;
        t1 ++ !t2 
    end
  | TEif (e1, e2, e3) -> let l_true = new_label() and l_end = new_label() in 
    expr env e1 ++ 
    testq (reg rdi) (reg rdi) ++ 
    jne l_true ++ 
    expr env e3 ++ 
    jmp l_end ++ 
    label l_true ++ 
    expr env e2 ++ 
    label l_end 

  | TEfor (e1, e2) -> let loop = new_label () and exit = new_label () in 
    label loop ++ 
    expr env e1 ++ 
    testq (reg rdi) (reg rdi) ++
    je exit ++ 
    expr env e2 ++
    jmp loop ++ 
    label exit
    
  | TEnew ty ->
    malloc (sizeof ty) ++ movq (reg rax) (reg rdi)

  | TEcall (f, el) ->
     (* TODO code pour appel fonction *) assert false

  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false

  | TEvars _ ->
     assert false (* fait dans block *)

  | TEreturn [] ->
    (* TODO code pour return e *) assert false

  | TEreturn [e1] ->
    (* TODO code pour return e1,... *) assert false

  | TEreturn _ ->
     assert false

  | TEincdec (e1, op) ->
    (if op = Inc then incq else decq) (reg rdi)
    (* TODO code pour return e++, e-- *) 

and decl_var env text = function
    | [] -> text
    | v::q -> (v.v_addr <- !env.next_local-8);  incr !env.nb_locals; !env.next_local <- !env.next_local - 8; 
              decl_var env (text ++ pushq (imm 0)) q
  

  

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  (* TODO code pour fonction *) let s = f.fn_name in label ("F_" ^ s) ++ expr empty_env e

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code

let file ?debug:(b=false) dl =
  debug := b;
  (* TODO calcul offset champs *)
  (* TODO code fonctions *) let funs = List.fold_left decl nop dl in
  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      funs ++
      inline "
print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret
print_string: 
	      movq %rdi, %rsi
	      movq $S_string, %rdi
	      xorq %rax, %rax
	      call printf
	      ret
"; (* TODO print pour d'autres valeurs *)
   (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld" ++
      label "S_string" ++ string "%s" ++ 
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
