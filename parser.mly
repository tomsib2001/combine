
%{
  open Ast
  open Tiling.Tile
  type option =
    | M of multiplicity
    | S of symetries

%}

%token PATTERN PROBLEM CONSTANT FALSE TRUE
%token SET SHIFT CROP RESIZE
%token MINUS AMPAMP BARBAR HAT DIFF UNION XOR INTER ONE MAYBE SYM
%token EQUAL LSBRA RSBRA RPAR LPAR COMMA
%token <string> IDENT
%token <int * int> DIM
%token <bool array array> ASCII
%token EOF

%nonassoc UNION INTER DIFF XOR prec_crop
%left AMPAMP MINUS BARBAR HAT

%start <Ast.file> file

%%
file:
  l = list(decl); EOF { l }
;

decl:
| PATTERN; id = IDENT; EQUAL; e = expr
    { Pattern (id, e) }
| PROBLEM; id = IDENT; EQUAL; e = expr; tl = tile_list
    { Problem (id, e, tl) }
;

option:
| ONE   { M Mone }
| MAYBE { M Mmaybe }
| SYM   { S Sall }

tile_list:
| LSBRA; l = separated_list(COMMA, tile); RSBRA { l }
;

tile:
| e = expr; o = list(option)
    { let option (s, m) = function
        | M m' -> s, m' (* FIXME: fail on ambiguity *)
	| S s' -> s', m (* idem *)
      in
      let s,m = List.fold_left option (Snone, Minf) o in
      e,s,m }
;

expr:
| LPAR; e = expr; RPAR { e }
| id = IDENT
    { Var id }
| CONSTANT; d = DIM; b = bool
    { let w,h = d in Constant (Array.make h (Array.make w b)) }
| UNION; e1 = expr; e2 = expr
    { Binary (Union, e1, e2) }
| INTER; e1 = expr; e2 = expr
    { Binary (Inter, e1, e2) }
| DIFF; e1 = expr; e2 = expr
    { Binary (Diff, e1, e2) }
| XOR; e1 = expr; e2 = expr
    { Binary (Xor, e1, e2) }
| e1 = expr; MINUS ;e2 = expr
    { Binary (Diff, e1, e2) }
| e1 = expr; AMPAMP ;e2 = expr
    { Binary (Inter, e1, e2) }
| e1 = expr; BARBAR ;e2 = expr
    { Binary (Union, e1, e2) }
| e1 = expr; HAT ;e2 = expr
    { Binary (Xor, e1, e2) }
| SET; e = expr; d = DIM; b = bool
    { SetOp (SetXY (b), d, e) }
| CROP; pos = DIM ;d = DIM; e = expr; %prec prec_crop
    { SetOp (Crop(pos), d, e)}
| SHIFT; e = expr; d = DIM
    { SetOp (Shift, d, e) }
| RESIZE; e = expr; d = DIM
    { SetOp (Resize, d, e) }
| a = ASCII
    { Constant a }
;

bool:
| FALSE { false }
| TRUE  { true  }
;

