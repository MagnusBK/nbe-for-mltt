open Sexplib

type uni_level = int
type t =
  | Var of int (* DeBruijn indices for variables *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Bool | True | False | If of (* BINDS *) t * t * t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sig of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Uni of uni_level

type env = t list

exception Illformed

let find_idx ~equal key xs =
  let rec go i = function
    | [] -> None
    | x :: xs ->
      if equal key x then Some i else go (i + 1) xs in
  go 0 xs

let of_sexp sexp =
  let rec syn_of_int = function
    | 0 -> Zero
    | n -> Suc (syn_of_int (n - 1)) in
  let rec construct_let env defs body = match defs with
    | [] -> go env body
    | Sexp.List [Sexp.Atom x; def] :: defs ->
      Let (go env def, construct_let (x :: env) defs body)
    | _ -> raise Illformed
  and go env = function
    | Sexp.Atom "Nat" -> Nat
    | Sexp.Atom "zero" -> Zero
    | Sexp.Atom var ->
      begin
        match int_of_string_opt var with
        | Some i when i >= 0 -> syn_of_int i
        | _ ->
          match find_idx ~equal:String.equal var env with
          | Some idx -> Var idx
          | None -> raise Illformed
      end
    | Sexp.List [Sexp.Atom "let"; Sexp.List def_tele; body] ->
      construct_let env def_tele body
    | Sexp.List [Sexp.Atom "check"; term; tp] ->
      Check (go env term, go env tp)
    | Sexp.List [Sexp.Atom "suc"; t] -> Suc (go env t)
    | Sexp.List
        [Sexp.Atom "nrec";
         Sexp.List [Sexp.Atom mVar; motive];
         zero;
         Sexp.List [Sexp.Atom pVar; Sexp.Atom indVar; succ];
         n] ->
      NRec
        (go (mVar :: env) motive,
         go env zero,
         go (indVar :: pVar :: env) succ,
         go env n)
    | Sexp.List [Sexp.Atom "Pi"; src; Sexp.List [Sexp.Atom x; dest]] ->
      Pi (go env src, go (x :: env) dest)
    | Sexp.List [Sexp.Atom "lam"; Sexp.List [Sexp.Atom x; body]] ->
      Lam (go (x :: env) body)
    | Sexp.List (Sexp.Atom "ap" :: f :: args) ->
      List.fold_left (fun f a -> Ap (f, go env a)) (go env f) args
    | Sexp.List [Sexp.Atom "Sig"; src; Sexp.List [Sexp.Atom x; dest]] ->
      Sig (go env src, go (x :: env) dest)
    | Sexp.List [Sexp.Atom "pair"; l; r] ->
      Pair (go env l, go env r)
    | Sexp.List [Sexp.Atom "fst"; t] ->
      Fst (go env t)
    | Sexp.List [Sexp.Atom "snd"; t] ->
      Snd (go env t)
    | Sexp.List [Sexp.Atom "U"; Sexp.Atom i] ->
      begin
        match int_of_string_opt i with
        | Some i when i >= 0 -> Uni i
        | _ -> raise Illformed
      end
    | _ -> raise Illformed in
  go [] sexp

let to_sexp env t =
  let counter = ref 0 in
  let rec int_of_syn = function
    | Zero -> Some 0
    | Suc t ->
      begin
        match int_of_syn t with
        | Some i -> Some (i + 1)
        | None -> None
      end
    | _ -> None in
  let rec go env = function
    | Var i ->
      if i >= List.length env
      then Sexp.Atom ("free" ^ string_of_int i)
      else List.nth env i
    | Nat -> Sexp.Atom "Nat"
    | Let (def, body) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List
        [Sexp.Atom "let";
         Sexp.List [var; go env def];
         go (var :: env) body]
    | Check (term, tp) -> Sexp.List [Sexp.Atom "check"; go env term; go env tp]
    | Zero -> Sexp.Atom "zero"
    | Suc t ->
      begin
        match int_of_syn t with
        | Some i -> Sexp.Atom (string_of_int (i + 1))
        | None -> Sexp.List [Sexp.Atom "suc"; go env t]
      end
    | NRec (motive, zero, suc, n) ->
      incr counter;
      let mvar = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let suc_var1 = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let suc_var2 = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List
        [Sexp.Atom "nrec";
         Sexp.List [mvar; go (mvar :: env) motive];
         go env zero;
         Sexp.List [suc_var1; suc_var2; go (suc_var2 :: suc_var1 :: env) suc];
         go env n]
    | Bool -> Sexp.Atom "Bool"
    | True -> Sexp.Atom "true"
    | False -> Sexp.Atom "false"
    | If (motive, tcase, fcase, prop) ->
      incr counter;
      let mvar = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List
        [Sexp.Atom "if";
         Sexp.List [mvar; go (mvar :: env) motive];
         go env tcase;
         go env fcase;
         go env prop]
    | Pi (src, dest) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Pi"; go env src; Sexp.List [var; go (var :: env) dest]]
    | Lam t ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "lam"; Sexp.List [var; go (var :: env) t]]
    | Ap (t1, t2) ->
      Sexp.List [Sexp.Atom "ap"; go env t1; go env t2]
    | Sig (fst, snd) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Sig"; go env fst; Sexp.List [var; go (var :: env) snd]]
    | Pair (t1, t2) ->
      Sexp.List [Sexp.Atom "pair"; go env t1; go env t2]
    | Fst t -> Sexp.List [Sexp.Atom "fst"; go env t]
    | Snd t -> Sexp.List [Sexp.Atom "snd"; go env t]
    | Uni i -> Sexp.List [Sexp.Atom "U"; Sexp.Atom (string_of_int i)] in
  go env t

let pp t = to_sexp [] t |> Sexp.to_string_hum
