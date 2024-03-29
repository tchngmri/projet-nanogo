open Format
open Lib
open Ast
open Tast
open Hashtbl
let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))

let rec sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tstruct s -> Hashtbl.fold (fun _ a b -> b + sizeof (a.f_typ)) s.s_fields 0
  | Tmany l -> List.fold_left (fun b a -> b + sizeof(a)) 0 l
  | _ -> assert false


let rec eq_type ty1 ty2 = match ty1, ty2 with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | Tmany l1, Tmany l2 -> begin
    match l1,l2 with 
    | [],[] -> true
    | x::q1, y::q2 -> (eq_type x y) && (eq_type (Tmany q1) (Tmany q2))
    | _ -> false 
  end 
  | Twild, _ | _,Twild -> true 
  | _ -> false


(* Environnement pour les structures : table de hachage *)
let struct_env = create 10

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | PTident { id = nom } -> match (find_opt struct_env nom) with 
                                | None -> error dummy_loc ("unknown struct")
                                | Some s -> Tstruct s

let pstruct_to_struct ps = 
  if mem struct_env ps.ps_name.id then find struct_env ps.ps_name.id else begin
  let sfields = create (List.length ps.ps_fields) in 
  let s = {s_name = ps.ps_name.id; s_fields = sfields; s_size = 0} in 
  let rec copy_fields ofs = function
			| [] -> ofs
			| (id, ptyp) :: q -> let f = { f_name = id.id; f_typ = (type_type ptyp); f_ofs = ofs}
				in if mem sfields id.id then error id.loc ("the field" ^ id.id ^ " is defined twice in structure " ^ s.s_name)
					else (add sfields id.id f;
						copy_fields (ofs + sizeof (f.f_typ)) q)
	in let size = copy_fields 0 ps.ps_fields in
	s.s_size <- size; s end

let fmt_used = ref false
let fmt_imported = ref false

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = 0; v_depth = 0 }

module Env = struct 
  module M = Map.Make(String)
  type t = var M.t
  let empty = M.empty
  let find = M.find
  let mem = M.mem
  let add env v = M.add v.v_name v env

  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && not(v.v_used) then error v.v_loc "unused variable" in 
    List.iter check !all_vars


  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

    (* TODO type () et vecteur de types *)
end

let func_env = create 10

let pfunc_to_func f = 
  let env = ref Env.empty in
		let pparam_to_var (id, ptyp) =
			if (Env.mem id.id !env)
			then error id.loc ("the name " ^ id.id ^ " is used twice in the arguments of the function " ^ f.pf_name.id)
			else
				let e, v = Env.var id.id id.loc (type_type ptyp) !env
				in env := e; v
		in let fn = { fn_name = f.pf_name.id;
					  fn_params = List.map pparam_to_var f.pf_params;
					  fn_typ = List.map type_type f.pf_typ }
		in fn, env

let add_func f = 
  if mem func_env f.pf_name.id then error f.pf_name.loc ("function "^f.pf_name.id^" defined twice")
  else begin 
    add func_env f.pf_name.id (fst (pfunc_to_func f))
  end 
  (*fonction qui ajoute la pfonction à l'environnement func_env, doit vérifier qu'elle est bien typée*)


let tvoid = Tmany []
let typeretour = ref tvoid
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid


let rec islvalue = function 
  | TEident _ -> true
  | TEdot (e,x) when islvalue e.expr_desc ->  true
  | TEunop(Ustar,e) when e.expr_desc != TEnil -> true
  | _ -> false

let rec flatten = function 
  | [] -> []
  | Tmany a ::q -> (flatten a)@(flatten q)
  | x::t-> x::(flatten t)


 let rec typetostr = function 
  | Tint -> "int"
  | Tbool -> "bool"
  | Tstring -> "string"
  | Tptr t -> "*"^(typetostr t)
  | Tstruct s -> s.s_name
  | Tmany [] -> "[]"
  | Tmany l ->
		let rec aux s = function
			| [] -> s ^ "]"
			| [t] -> s ^ (typetostr t) ^ "]"
			| t :: q -> aux (s ^ (typetostr t) ^ ", ") q
		in aux "[" l
  | Twild -> "??????" 
let errortype loc exp real = 
  error loc ("this expression has type"^(typetostr real)^" but is expected to have type"^(typetostr exp))

let list_to_type = function 
| [t] -> t 
| l -> Tmany l 

let rec expr env e =
 let e, ty, rt = (expr_desc env (e.pexpr_loc) (e.pexpr_desc)) in
  { expr_desc = e; expr_typ = ty }, rt
  and expr_desc env loc = function 
  | PEskip -> 
     TEskip, tvoid, false

  | PEconstant c -> 
    TEconstant c, (match c with 
      | Cbool _ -> Tbool
      | Cint _ -> Tint
      | Cstring _ -> Tstring), false

  | PEbinop (op, e1, e2) ->
    let a1,a2 = (expr env e1), (expr env e2) in 
    (match op with 
      | Badd | Bsub | Bmul | Bdiv | Bmod -> 
        (if (fst a1).expr_typ != Tint then (errortype loc Tint (fst a1).expr_typ)
        else (if (fst a2).expr_typ != Tint then (errortype loc Tint (fst a2).expr_typ)
        else (TEbinop (op,(fst a1),(fst a2))), Tint, false))
      | Beq | Bne -> 
        if ((fst a1).expr_typ = (fst a2).expr_typ)&&((fst a1).expr_desc != TEnil)&&((fst a2).expr_desc != TEnil) 
          then (TEbinop (op,(fst a1),(fst a2))), Tbool, false
        else (error loc "comparison between expressions of different types")
      | Blt | Ble | Bgt | Bge -> 
        (if (fst a1).expr_typ != Tint then (errortype loc Tint (fst a1).expr_typ)
        else (if (fst a2).expr_typ != Tint then (errortype loc Tint (fst a2).expr_typ)
        else (TEbinop (op,(fst a1),(fst a2))), Tbool, false))
      | Band | Bor -> 
        if (fst a1).expr_typ != Tbool then (errortype loc Tbool (fst a1).expr_typ) else 
        (if (fst a2).expr_typ != Tbool then (errortype loc Tbool (fst a2).expr_typ)
        else (TEbinop (op,(fst a1),(fst a2))),Tbool, false))

  | PEunop (Uamp, e1) -> let a = expr env e1 in 
    if (islvalue (fst a).expr_desc) then (TEunop (Uamp,(fst a)), Tptr (fst a).expr_typ, false) 
    else (error loc "l-value required")

  | PEunop (Uneg | Unot | Ustar as op, e1) ->
      let e2,_ = expr env e1 in (TEunop (op, e2), (match e2.expr_typ with 
      | Tint -> if op = Uneg then Tint else (error loc "type int attendu") 
      | Tbool -> if op = Unot then Tbool else (error loc "type bool attendu") 
      | Tptr(t) -> if (op = Ustar)&&(e2.expr_desc != TEnil) then t else error loc "jsp quoi écrire"
      | _ -> error loc "aaaaaa laide"),false)

  | PEcall ({id = "fmt.Print"}, el) -> if not(!fmt_imported) then error loc  "fmt n'a pas été importé"
  else (fmt_used := true; let aafficher = List.map (fun e -> (fst (expr env e))) el in 
    TEprint aafficher, tvoid, false)

  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) ->
     let ty = match id with
       | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
       | _ when mem struct_env id -> Tstruct (find struct_env id)
       | _ ->  error loc ("no such type " ^ id) in
     TEnew ty, Tptr ty, false

  | PEcall ({id="new"}, _) ->
     error loc "new expects a type"

  | PEcall (id, el) -> if not (mem func_env id.id) then error loc ("function "^id.id^" is undefined") 
    else (
      let arg = List.map (fun e -> (fst (expr env e))) el  and f = find func_env id.id in  
      let n = List.length f.fn_params in
		  let k = List.length (List.map (fun e -> (fst(expr env e)).expr_typ) el) in
		  if k < n then error id.loc ("missing arguments in calling function " ^ f.fn_name ^ ": " ^ (string_of_int k) ^ " were given but " ^ (string_of_int n) ^ " were expected")
			else if k > n then error id.loc ("too many arguments in calling function " ^ f.fn_name ^ ": " ^ (string_of_int k) ^ " were given but " ^ (string_of_int n) ^ " were expected")
			else begin
				let given_types = list_to_type(flatten (List.map (fun e -> e.expr_typ) arg)) in
				let expected_types = list_to_type (List.map (fun v -> v.v_typ) f.fn_params) in
				if (eq_type given_types expected_types)
				then TEcall(f, arg), list_to_type (f.fn_typ), false
				else error id.loc ("wrong argument types in calling function " ^ f.fn_name ^ ": " ^ (typetostr given_types) ^ " was given but " ^ (typetostr expected_types) ^ " was expected")
			end)

  | PEfor (e, b) ->
    let expe, re = expr env e and expb, rb = expr env b in 
    if re || expe.expr_typ != Tbool then error loc "condition of type bool expected after a for" else 
      TEfor(expe, expb),tvoid,rb

  | PEif (e1, e2, e3) -> let exp1,r1 = expr env e1 and exp2,r2 = expr env e2 and exp3,r3 = expr env e3 in 
    if exp1.expr_typ != Tbool then errortype loc Tbool exp1.expr_typ 
    else ((TEif (exp1, exp2,exp3)), (if r2&&r3 then exp2.expr_typ else tvoid) ,r2&&r3)

  | PEnil ->
     TEnil, tvoid, false

  | PEident {id=id} ->
      (try (let v = Env.find id !env in v.v_used <- true; TEident v, v.v_typ, false)
      with Not_found -> error loc ("unbound variable " ^ id))

  | PEdot (e, id) ->
     let exp,r = expr env e in 
     (match exp.expr_typ with 
     | Tstruct s | Tptr Tstruct s when exp.expr_desc != TEnil -> 
      (match find_opt s.s_fields id.id with 
        | None -> error loc "undefined field"
        | Some f -> TEdot(exp,f), f.f_typ, false )
     | _ -> error loc "a structure was expected")

  | PEassign (lvl, el) -> 
    begin 
		let rec aux l1 l2 = function
			| [], [] -> l1, l2
			| lv :: ql, e :: qe ->
        let explv, rtlv = expr env lv and expe, rte = expr env e in
				if islvalue explv.expr_desc
				then match explv.expr_desc with
						| TEident v ->
							if v.v_typ = expe.expr_typ then aux (explv :: l1) (expe :: l2) (ql, qe)
							else error e.pexpr_loc ("types don't match in the assignement : " ^ (typetostr expe.expr_typ) ^ " was given but " ^ (typetostr v.v_typ) ^ " was expected")
						| TEdot (exp, f) -> 
	              if f.f_typ = expe.expr_typ then aux (explv :: l1) (expe :: l2) (ql, qe)
										else error e.pexpr_loc ("types don't match in the assignment, " ^ (typetostr expe.expr_typ) ^ " was given but " ^ (typetostr f.f_typ) ^ " was expected")
						| _ -> error lv.pexpr_loc ("only variables and structure fields can be assigned")
				else error lv.pexpr_loc ("only l-calues can be assigned")
			| _ -> error loc ("unmatching number of arguments in the assignement")
			in let lvl2, el2 = aux [] [] (lvl, el) in
			TEassign(lvl2, el2), tvoid, false
	end

  | PEreturn el -> 
    let expl = List.map (fun e -> fst (expr env e)) el in
		let typs = list_to_type (List.map (fun exp -> exp.expr_typ) expl) in
    if typs = !typeretour 
      then TEreturn expl, tvoid, true
      else error loc ("this function is expected to return "^typetostr !typeretour^" but here it returns type "^typetostr typs)

  | PEblock el -> 
    let expl = List.map (fun x-> fst (expr env x)) el in
    let rt = List.exists (fun x -> snd (expr env x)) el in
    (*environnement ? *)
    TEblock expl, tvoid, rt

  | PEincdec (e, op) -> let exp = expr env e in 
    if not(islvalue (fst exp).expr_desc) then error loc "this expression needs to be a l-value" else(
      if not(eq_type (fst exp).expr_typ Tint) then error loc "this expression needs to have type int" else 
        TEincdec((fst exp), op),Tint, false
    )

  | PEvars (idl,None,pl) ->
     if (pl=[]) then error loc "empty declaration with no type"
     else
      let typelist = List.map (fun pexp -> (fst (expr env pexp)).expr_typ) pl  
      and exprlist = List.map (fun pexp -> fst (expr env pexp)) pl in 
      (try (
        let var = List.map2 (fun x y -> let newvar = Env.var x.id x.loc y !env in
        env := fst newvar;
        snd newvar) 
        idl (flatten typelist) in
        TEvars(var, exprlist),Tmany(typelist),false)
      with (Invalid_argument _) -> error loc "number of variables doesn't match the number of expressions" ) 

  | PEvars(ids,Some pt,pexprs) -> 
    let p = type_type pt 
    and exprlist = List.map (fun pexp -> fst (expr env pexp)) pexprs in 
    TEvars(
      (List.map 
        (fun x -> 
          let newvar = Env.var x.id x.loc p !env in
          env := fst newvar;
          snd newvar) ids), exprlist),
    tvoid,false
    

let found_main = ref false

(* 1. declare structures *)
let phase1 = function
  | PDstruct ({ ps_name = { id ; loc } ; ps_fields} as ps) -> if mem struct_env id then error loc ("structure "^id^" defined twice") else
    let s = pstruct_to_struct ps in add struct_env id s;
  | PDfunction _ -> ()

let rec sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tstruct s -> Hashtbl.fold (fun _ a b -> b + sizeof (a.f_typ)) s.s_fields 0
  | Tmany l -> List.fold_left (fun b a -> b + sizeof(a)) 0 l
  | _ -> assert false

(* 2. declare functions and type fields *)

let phase2 = function
  | PDfunction ({ pf_name={id; loc}; pf_params=pl; pf_typ=tyl; } as f) -> 
      (if f.pf_name.id = "main" then 
        (if f.pf_params!=[] then error f.pf_name.loc "main function can't be given arguments"
         else (if (f.pf_typ != []) then error f.pf_name.loc "main function can't return anything" 
               else found_main:=true)));
    add_func f
  | PDstruct { ps_name = {id}; ps_fields = fl } ->
     (* TODO *) () 

(* 3. type check function bodies *)
let decl = function
  | PDfunction ({ pf_name={id; loc}; pf_body = e; pf_typ=tyl } as pf) ->
    (* TODO check name and type *) 
    let f, env = pfunc_to_func pf in
		typeretour := list_to_type f.fn_typ;
		let e, rt = expr env pf.pf_body in
		if (f.fn_typ <> []) && (not rt)
		then error pf.pf_name.loc ("this function is expected to return something")
		else TDfunction (f, e)
  | PDstruct ps -> TDstruct (pstruct_to_struct ps)

let file ~debug:b (imp, dl) =
  debug := b;
  fmt_imported := imp;
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  (*Env.check_unused (); TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl

