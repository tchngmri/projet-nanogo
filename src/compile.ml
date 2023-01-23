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

let fun_env f =
    { empty_env with exit_label = "E_" ^ f.fn_name; nb_locals= ref 0}

let mk_bool d = { expr_desc = d; expr_typ = Tbool } (* crée expression expr de type Tbool à partir d'une expr_desc de type bool *)
let mk_int i = { expr_desc = i; expr_typ = Tint } (* crée expression expr de type Tint à partir d'une expr_desc de type int *)

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
    movq (imm 1) (reg rdi) (* on renvoie toujours le résultat dans le registre rdi *)

  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)

  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)

  | TEnil ->
    xorq (reg rdi) (reg rdi)

  | TEconstant (Cstring s) -> (* on alloue de la mémoire, on crée la chaine de caractère et on la stocke dans rdi *)
    let labelstring = alloc_string s in 
      movq (ilab labelstring) (reg rdi) 
  
  | TEbinop (Band, e1, e2) -> (* et lazy : on évalue e2 que si e1 est vraie *)
    expr env (mk_bool(TEif (e1, e2, mk_bool (TEconstant (Cbool false)))))
    
  | TEbinop (Bor, e1, e2) -> (* ou lazy : on évalue e2 que si e1 est faux *)
    expr env (mk_bool(TEif (e1, mk_bool (TEconstant (Cbool true)), e2)))
   
  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) ->
    expr env e1 ++ 
    pushq (reg rdi) ++ 
    expr env e2 ++ 
    popq (rax) ++ 
    cmpq (reg rdi) (reg rax) ++ (* on compare les expressions, puis on appelle compile_bool avec le bon drapeau *)
    compile_bool ( match op with 
    | Blt -> js 
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
              popq (rdi) ++ 
              addq (reg rax) (reg rdi) 
    | Bsub -> movq (reg rdi) (reg rax) ++ 
              popq (rdi) ++
              subq (reg rax) (reg rdi)
    | Bmul -> movq (reg rdi) (reg rax) ++ 
              popq (rdi) ++ 
              imulq (reg rax) (reg rdi)
    | Bdiv -> popq (rax) ++ 
              xorq (reg rdx) (reg rdx) ++ 
              idivq (reg rdi) ++ 
              movq (reg rax) (reg rdi)
    | Bmod -> popq (rax) ++ 
              xorq (reg rdx) (reg rdx) ++  
              idivq (reg rdi) ++ 
              movq (reg rdx) (reg rdi)
    | _ -> assert false)

  | TEbinop (Beq | Bne as op, e1, e2) -> 
    expr env e1 ++ 
    pushq (reg rdi) ++
    expr env e2 ++ 
    (match e1.expr_typ with (* comparaison en fonction du type... ici, que les eniters ! *)
      | Tint | Tbool -> (
        popq (rax) ++
        cmpq (reg rdi) (reg rax) ++
        compile_bool (match op with 
          | Beq -> je
          | Bne -> jne
          | _ -> assert false )) 
      | Tstring -> assert false (* pas sûre de savoir faire... *)
      | _ -> assert false 
      )

  | TEunop (Uneg, e1) ->
    expr env e1 ++  
    negq (reg rdi) 

  | TEunop (Unot, e1) ->
    expr env e1 ++ 
    notq (reg rdi)

  | TEunop (Uamp, e1) -> 
    (match e1.expr_desc with
    | TEident x -> leaq (ind ~ofs:(x.v_addr) rbp) rdi (* x est stockée dans la pile avec un offset stocké dans x.v_addr, il suffit d'utiliser leaq pour récupérer l'adresse *)
    | TEunop (Ustar, e) -> expr env e (* l'adresse du pointeur est sa valeur ! *)
    | _ -> assert false)

  | TEunop (Ustar, e1) ->
      (expr env e1) ++ movq (ind rdi) (reg rdi) (* on remplace rdi par son adresse *)

  | TEprint el -> (* différents print sont à traiter : ici, on ne fait que int et string *)
    (match el with 
      | [] -> nop
      | x::q -> begin expr env x ++ 
        (match x.expr_typ with 
          | Tint | Tbool -> call "print_int" (* print_int et print_string sont définis à la fin du fichier dans la fonciton file *)      
          | Tstring ->  call "print_string" 
          | _ -> nop) ++ 
        expr env ({expr_desc = TEprint q; expr_typ = tvoid})
      end)

  | TEident x -> (* on récupère le contenu de x dans la pile, son offset étant stocké dans x.v_addr *)
    movq (ind ~ofs:(x.v_addr) rbp) (reg rdi) 

  | TEassign ([{expr_desc=TEident x}], [e1]) -> (* on évalue e1, puis on le stocke à l'emplacement de x dans la pile *)
    expr env e1 ++
    movq (reg rdi) ((ind ~ofs:x.v_addr rbp)) 

  | TEassign (lv, el) -> (* on sait que lv et el sont de même longueue après l'étape du typage *)
    let rec aux = function 
      | [],[] -> nop 
      | ({expr_desc=TEident x}::lv, e1::el) -> (* on fait de même que précédemment, mais en itérant pour chaque variable *)
        expr env e1 ++
        movq (reg rdi) ((ind ~ofs:x.v_addr rbp)) ++ aux (lv,el) 
      in aux (lv,el)

  | TEblock el -> begin
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

  | TEif (e1, e2, e3) -> 
    let l_true = new_label() and l_end = new_label() in 
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
    jz exit ++ 
    expr env e2 ++
    jmp loop ++ 
    label exit
    
  | TEnew ty ->
    malloc (sizeof ty) ++ 
    movq (reg rax) (reg rdi)

  | TEcall (f, el) -> (* appel de fonction : on place tous les arguments sur la pile puis on sauvegarde %rbp et on appelle la fonction *)
    let l1 = List.fold_left (push_params env) nop el in
    l1 ++ call ("F_"^(f.fn_name)) ++ addq (imm ((List.length el)*8)) !%rsp

  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false

  | TEvars _ -> (* fait dans block *)
     assert false 

  | TEreturn [] ->
    jmp env.exit_label

  | TEreturn [e1] ->
    expr env e1 ++ jmp env.exit_label

  | TEreturn el ->
    (List.fold_left (fun c exp ->
      c ++
      expr env exp ++
      pushq (reg rdi)) nop el) ++
    jmp env.exit_label

  | TEincdec (e1, op) ->
      match op with (* on distngue les cas incrémentation ét décrémentation*)
      | Inc ->
          expr env e1
          ++ incq (reg rdi) (*on évalue les parametres et on les met sur la pile*)
          ++ pushq (reg rdi) (*met resultat sur la pile*)
          ++ expr env (mk_int (TEunop (Uamp, e1))) (*recup adresse variable*)
          ++ popq rbx (*recup valeur ++*)
          ++ movq (reg rbx) (ind rdi) (*met valeur ++ à l'adresse de la variable*)
      | Dec ->
          expr env e1
          ++ decq (reg rdi)
          ++ pushq (reg rdi)
          ++ expr env (mk_int (TEunop (Uamp, e1)))
          ++ popq rbx
          ++ movq (reg rbx) (ind rdi)

and decl_var env text = function
    | [] -> text
    | v::q -> (v.v_addr <- !env.next_local-8); !env.next_local <- !env.next_local - 8; 
              decl_var env (text ++ pushq (imm 0)) q
and push_params env init e = init ++ expr env e ++ pushq (reg rdi)
  

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  let s = f.fn_name in 
  let env = fun_env f in
  let arg_addr = ref ((List.length f.fn_params) * 8 + 8) in
  List.iter (fun v -> v.v_addr <- !arg_addr; arg_addr := !arg_addr - 8) f.fn_params;
    label ("F_" ^ s) ++
    pushq (reg rbp) ++
    movq (reg rsp) (reg rbp) ++
    expr env e ++
    label ("E_" ^ s) ++
    movq (reg rbp) (reg rsp) ++
    popq rbp ++
    ret

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
