
open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))

(* TODO environnement pour les types structure *)
let struct_env = Hashtbl.create(10) (* Table de hachage qui contient des (string, structure) *)
(* est ce qu'il faut faire une table de hachage ou un module ?? c quoi la diff ? *)

(* TODO environnement pour les fonctions *)
let funct_env = Hashtbl.create(10) (* Table de hachage, contient des (string, function) *)

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | PTident { id = nom } -> match (Hashtbl.find_opt struct_env nom) with 
                                | None -> error dummy_loc ("unknown struct")
                                | Some s -> Tstruct s
 (* TODO type structure *)

let rec eq_type ty1 ty2 = match ty1, ty2 with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | _ -> false
    (* TODO autres types *) (* ??? *)

let fmt_used = ref false
let fmt_imported = ref false

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = 0; v_depth = 0 }

module Env = struct (* est ce qu'on définit une structure là ? *)
  module M = Map.Make(String)
  type t = var M.t
  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env

  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && not(v.v_used) (*TO DO used*) then error v.v_loc "unused variable" in 
    List.iter check !all_vars


  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

    
    (* TODO type () et vecteur de types *)
end

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid


let rec islvalue x = true (* fonction qui détermine si c'est une l value... comment faire ? *)


let rec expr env e =
 let e, ty, rt = (expr_desc env (e.pexpr_loc) (e.pexpr_desc)) in
  { expr_desc = e; expr_typ = ty }, rt
(* rt check si ya un return *)
  and expr_desc env loc = function (*refaire les erreurs pour qu'elles affichent type voulu...*)
  | PEskip -> 
     TEskip, tvoid, false
  | PEconstant c -> 
    TEconstant c, (match c with 
      | Cbool _ -> Tbool
      | Cint _ -> Tint
      | Cstring _ -> Tstring), false
    (* TODO *) 
  | PEbinop (op, e1, e2) ->
    let a1,a2 = (expr env e1), (expr env e2) in 
    (TEbinop (op,(fst a1),(fst a2))), (match op with 
    | Badd | Bsub | Bmul | Bdiv | Bmod -> 
      (if (fst a1).expr_typ != Tint || (fst a2).expr_typ != Tint then (error loc "type int attendu ici")
      else Tbool)
    | Beq | Bne -> 
      if ((fst a1).expr_typ == (fst a2).expr_typ)&&((fst a1).expr_desc != TEnil)&&((fst a2).expr_desc != TEnil) 
        then Tbool 
      else (error loc "les deux expressions doivent avoir le même type")
    | Blt | Ble | Bgt | Bge -> 
      if (fst a1).expr_typ != Tint || (fst a2).expr_typ != Tint then (error loc "type int attendu ici") 
      else Tbool
    | Band | Bor -> 
      if (fst a1).expr_typ != Tbool || (fst a2).expr_typ != Tbool then (error loc "type bool attendu ici") 
      else Tbool), false
    (* TODO *) 
  | PEunop (Uamp, e1) -> let a = expr env e1 in 
    if (islvalue e1.pexpr_desc) then (TEunop (Uamp,(fst a)), Tptr (fst a).expr_typ, false) 
    else error loc "l-value attendue pour prendre l'adresse" 
    (* TODO *) 
    | PEunop (Uneg | Unot | Ustar as op, e1) ->
      let e2,_ = expr env e1 in (Teunop (op, e2), (match e2.expr_typ with 
      | Tint -> if op == Uneg then Tint else (error loc "type int attendu") 
      | Tbool -> if op == Unot then Tbool else (error loc "type bool attendu") 
      | Tptr(t) -> if (op == Ustar)&&(e2.expr_typ != TEnil) then t else error loc "jsp quoi écrire"
      | _ -> error loc "aaaaaa laide"),false)
      (* TODO *)
  | PEcall ({id = "fmt.Print"}, el) -> if not(!fmt_imported) then error loc  "fmt n'a pas été importé"
  else fmt_used := true; let aafficher = List.map (fun e -> (fst (expr env e))) el in 
    (* TODO *) TEprint aafficher, tvoid, false
  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) ->
     let ty = match id with
       | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
       | _ -> (* TODO : j'ai pas comprs ce que faisait new*) error loc ("no such type " ^ id) in
     TEnew ty, Tptr ty, false
  | PEcall ({id="new"}, _) ->
     error loc "new expects a type"
  | PEcall (id, el) ->
     (* TODO *) assert false
  | PEfor (e, b) ->
     (* TODO *) assert false
  | PEif (e1, e2, e3) ->
     (* TODO *) assert false
  | PEnil ->
     (* TODO *) assert false
  | PEident {id=id} ->
     (* TODO *) (try let v = Env.find id env in TEident v, v.v_typ, false
      with Not_found -> error loc ("unbound variable " ^ id))
  | PEdot (e, id) ->
     (* TODO *) assert false
  | PEassign (lvl, el) -> 
     (* TODO *) TEassign ([], []), tvoid, false 
  | PEreturn el -> 
     (* TODO *) TEreturn [], tvoid, true
  | PEblock el -> 
     (* TODO *) TEblock [], tvoid, false
  | PEincdec (e, op) -> 
     (* TODO *) assert false
  | PEvars _ ->
     (* TODO *) assert false 

let found_main = ref false

(* 1. declare structures *)
let phase1 = function
  | PDstruct ({ ps_name = { id = id; loc = loc }} as s) -> if Hashtbl.mem struct_env id then 
    error loc ("structure "^id^" has already been defined")
    else Hashtbl.add struct_env id s
  | PDfunction _ -> ()

let rec sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tstruct s -> Hashtbl.fold (fun _ a b -> b + sizeof (a.f_typ)) s.s_fields 0
  | Tmany l -> List.fold_left (fun b a -> b + sizeof(a)) 0 l 
(* TODO *) 

(* 2. declare functions and type fields *)
let phase2 = function
  | PDfunction { pf_name={id; loc}; pf_params=pl; pf_typ=tyl; } ->
     (* TODO *) ()
  | PDstruct { ps_name = {id}; ps_fields = fl } ->
     (* TODO *) () 

(* 3. type check function bodies *)
let decl = function
  | PDfunction { pf_name={id; loc}; pf_body = e; pf_typ=tyl } ->
    (* TODO check name and type *) 
    let f = { fn_name = id; fn_params = []; fn_typ = []} in
    let e, rt = expr Env.empty e in
    TDfunction (f, e)
  | PDstruct {ps_name={id}} ->
    (* TODO *) let s = { s_name = id; s_fields = Hashtbl.create 5; s_size = 0 } in
     TDstruct s

let file ~debug:b (imp, dl) =
  debug := b;
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env.check_unused (); (* TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl


  (* note : vérifier l'importation de fmt en dehors de la fonction expr*)