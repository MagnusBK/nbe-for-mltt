type uni_level = int
type t =
  | Var of int (* DeBruijn indices for variables *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sig of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Uni of uni_level

type env = t list

exception Illformed
val of_sexp : Sexplib.Sexp.t -> t
val to_sexp : Sexplib.Sexp.t list -> t -> Sexplib.Sexp.t
val pp : t -> string
