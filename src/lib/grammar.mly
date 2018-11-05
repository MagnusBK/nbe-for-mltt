%{
  open Concrete_syntax
%}

%token <int> NUMERAL
%token <string> ATOM
%token COLON PIPE AT COMMA RIGHT_ARROW UNDERSCORE
%token LPR RPR LBR RBR LANGLE RANGLE
%token EQUALS
%token TIMES FST SND
%token LAM LET IN WITH DEF
%token REC SUC NAT ZERO
%token UNIV
%token QUIT NORMALIZE
%token EOF

%start <Concrete_syntax.signature> sign
%%

name:
  | s = ATOM
    { s }
  | UNDERSCORE
    { "_" }

decl:
  | LET; nm = name; COLON; tp = term; EQUALS; body = term
    { Def {name = nm; def = body; tp} }
  | QUIT { Quit }
  | NORMALIZE; DEF; a = name
    { NormalizeDef a  }
  | NORMALIZE; tm = term; AT; tp = term { NormalizeTerm {term = tm; tp} };

sign:
  | EOF { [] }
  | d = decl; s = sign { d :: s };

atomic:
  | LPR; t = term; RPR
    { t }
  | LBR; t = term; AT; tp = term RBR
    { Check {term = t; tp} }
  | a = name
    { Var a }
  | ZERO
    { Lit 0 }
  | n = NUMERAL
    { Lit n }
  | UNIV; LANGLE; i = NUMERAL; RANGLE
    { Uni i }
  | NAT { Nat }
  | LANGLE left = term; COMMA; right = term; RANGLE
    { Pair (left, right) };

spine:
  | t = atomic { t }

term:
  | f = atomic; args = list(spine)
    { Ap (f, args) }
  | LET; name = name; COLON; tp = term; EQUALS; def = term; IN; body = term
    { Let (Check {term = def; tp}, Binder {name; body}) }
  | LET; name = name; EQUALS; def = term; IN; body = term
    { Let (def, Binder {name; body}) }
  | LPR t = term; AT; tp = term RPR
    { Check {term = t; tp} }
  | SUC; t = term { Suc t }
  | REC; n = term; AT; mot_name = name; RIGHT_ARROW; mot = term; WITH;
    PIPE; ZERO; RIGHT_ARROW; zero_case = term;
    PIPE; SUC; suc_var = name; COMMA; ih_var = name; RIGHT_ARROW; suc_case = term
    { NRec {
        mot = Binder {name = mot_name; body = mot};
        zero = zero_case;
        suc = Binder2 {name1 = suc_var; name2 = ih_var; body = suc_case};
        nat = n
      } }
  | LAM; name = name; RIGHT_ARROW; body = term
    { Lam (Binder {name; body}) }
  | LPR name = name; COLON; dom = term; RPR; RIGHT_ARROW; cod = term
    { Pi (dom, Binder {name; body = cod}) }
  | LPR name = name; COLON; left = term; RPR; TIMES; right = term
    { Sig (left, Binder {name; body = right}) }
  | dom = atomic RIGHT_ARROW; cod = term
    { Pi (dom, Binder {name = ""; body = cod}) }
  | left = atomic; TIMES; right = term
    { Sig (left, Binder {name = ""; body = right}) }
  | FST; t = term { Fst t }
  | SND; t = term { Snd t }
;
