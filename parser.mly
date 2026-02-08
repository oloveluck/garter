%{
open Exprs
%}

%token <int64> NUM
%token <string> ID
%token <string> STRING
%token DEF ANDDEF ADD1 SUB1 LPARENSPACE LPARENNOSPACE RPAREN LBRACK RBRACK LET IN EQUAL COMMA PLUS MINUS TIMES DIV MOD IF COLON ELSECOLON EOF PRINT PRINTSTACK TRUE FALSE ISBOOL ISNUM ISTUPLE EQEQ LESSSPACE GREATER LESSEQ GREATEREQ AND OR NOT COLONEQ SEMI NIL LAMBDA BEGIN END SHADOW REC UNDERSCORE MATCH ARROW BAR

%right SEMI
%left COLON COLONEQ
%left PLUS MINUS TIMES DIV MOD GREATER LESSSPACE GREATEREQ LESSEQ EQEQ AND OR
%left LPARENNOSPACE


%type <(Lexing.position * Lexing.position) Exprs.program> program

%start program

%%

const :
  | NUM { ENumber($1, ($startpos, $endpos)) }
  | TRUE { EBool(true, ($startpos, $endpos)) }
  | FALSE { EBool(false, ($startpos, $endpos)) }
  | NIL %prec SEMI { ENil(($startpos, $endpos)) }
  | STRING { EString($1, ($startpos, $endpos)) }

prim1 :
  | ADD1 { Add1 }
  | SUB1 { Sub1 }
  | NOT { Not }
  | PRINT { Print }
  | ISBOOL { IsBool }
  | ISNUM { IsNum }
  | ISTUPLE { IsTuple }
  | PRINTSTACK { PrintStack }

bindings :
  | bind EQUAL expr { [($1, $3, ($startpos, $endpos))] }
  | bind EQUAL expr COMMA bindings { ($1, $3, ($startpos($1), $endpos($3)))::$5 }

namebindings :
  | namebind EQUAL expr { [($1, $3, ($startpos, $endpos))] }
  | namebind EQUAL expr COMMA namebindings { ($1, $3, ($startpos($1), $endpos($3)))::$5 }

expr :
  | LET bindings IN expr { ELet($2, $4, ($startpos, $endpos)) }
  | LET REC namebindings IN expr { ELetRec($3, $5, ($startpos, $endpos)) }
  | IF expr COLON expr ELSECOLON expr { EIf($2, $4, $6, ($startpos, $endpos)) }
  | MATCH expr COLON match_cases { EMatch($2, $4, ($startpos, $endpos)) }
  | BEGIN expr END { $2 }
  | binop_expr SEMI expr { ESeq($1, $3, ($startpos, $endpos)) }
  | binop_expr { $1 }

match_cases :
  | match_case { [$1] }
  | match_case match_cases { $1 :: $2 }

match_case :
  | BAR pattern ARROW expr { ($2, $4) }

pattern :
  | UNDERSCORE { PWild(($startpos, $endpos)) }
  | ID { PVar($1, ($startpos, $endpos)) }
  | NUM { PNum($1, ($startpos, $endpos)) }
  | TRUE { PBool(true, ($startpos, $endpos)) }
  | FALSE { PBool(false, ($startpos, $endpos)) }
  | STRING { PString($1, ($startpos, $endpos)) }
  | NIL { PNil(($startpos, $endpos)) }
  | LPARENNOSPACE RPAREN { PTuple([], ($startpos, $endpos)) }
  | LPARENSPACE RPAREN { PTuple([], ($startpos, $endpos)) }
  | LPARENNOSPACE pattern COMMA RPAREN { PTuple([$2], ($startpos, $endpos)) }
  | LPARENSPACE pattern COMMA RPAREN { PTuple([$2], ($startpos, $endpos)) }
  | LPARENNOSPACE pattern COMMA patterns RPAREN { PTuple($2::$4, ($startpos, $endpos)) }
  | LPARENSPACE pattern COMMA patterns RPAREN { PTuple($2::$4, ($startpos, $endpos)) }

patterns :
  | pattern { [$1] }
  | pattern COMMA patterns { $1 :: $3 }

exprs :
  | expr { [$1] }
  | expr COMMA exprs { $1::$3 }

tuple_expr :
  | LPARENNOSPACE RPAREN { ETuple([], ($startpos, $endpos)) }
  | LPARENSPACE RPAREN { ETuple([], ($startpos, $endpos)) }
  | LPARENNOSPACE expr COMMA RPAREN { ETuple([$2], ($startpos, $endpos)) }
  | LPARENSPACE expr COMMA RPAREN { ETuple([$2], ($startpos, $endpos)) }
  | LPARENNOSPACE expr COMMA exprs RPAREN { ETuple($2::$4, ($startpos, $endpos)) }
  | LPARENSPACE expr COMMA exprs RPAREN { ETuple($2::$4, ($startpos, $endpos)) }

id :
  | ID %prec COLON { EId($1, ($startpos, $endpos)) }


prim2 :
  | PLUS { Plus }
  | MINUS { Minus }
  | TIMES { Times }
  | DIV { Div }
  | MOD { Mod }
  | AND { And }
  | OR { Or }
  | GREATER { Greater }
  | GREATEREQ { GreaterEq }
  | LESSSPACE { Less }
  | LESSEQ { LessEq }
  | EQEQ { Eq }

binop_expr :
  | binop_expr prim2 binop_operand %prec PLUS { EPrim2($2, $1, $3, ($startpos, $endpos)) }
  | binop_operand COLONEQ binop_expr %prec COLONEQ {
      match $1 with
      | EGetItem(lhs, idx, _) -> ESetItem(lhs, idx, $3, ($startpos, $endpos))
      | _ -> raise (Errors.ParseError (Printf.sprintf "Parse error: invalid assignment target at line %d" $startpos.Lexing.pos_lnum))
    }
  | binop_operand %prec PLUS { $1 }

binop_operand :
  // Primops
  | prim1 LPARENNOSPACE expr RPAREN { EPrim1($1, $3, ($startpos, $endpos)) }
  // Tuples
  | tuple_expr { $1 }
  | binop_operand LBRACK expr RBRACK { EGetItem($1, $3, ($startpos, $endpos)) }
  // Function calls
  | binop_operand LPARENNOSPACE exprs RPAREN %prec LPARENNOSPACE { EApp($1, $3, Unknown, ($startpos, $endpos)) }
  | binop_operand LPARENNOSPACE RPAREN %prec LPARENNOSPACE { EApp($1, [], Unknown, ($startpos, $endpos)) }
  // Parentheses
  | LPARENSPACE expr RPAREN { $2 }
  | LPARENNOSPACE expr RPAREN { $2 }
  // Lambdas
  | LPARENNOSPACE LAMBDA LPARENNOSPACE binds RPAREN COLON expr RPAREN { ELambda($4, $7, ($startpos, $endpos)) }
  | LPARENNOSPACE LAMBDA LPARENSPACE binds RPAREN COLON expr RPAREN { ELambda($4, $7, ($startpos, $endpos)) }
  | LPARENNOSPACE LAMBDA COLON expr RPAREN { ELambda([], $4, ($startpos, $endpos)) }
  | LPARENSPACE LAMBDA LPARENNOSPACE binds RPAREN COLON expr RPAREN { ELambda($4, $7, ($startpos, $endpos)) }
  | LPARENSPACE LAMBDA LPARENSPACE binds RPAREN COLON expr RPAREN { ELambda($4, $7, ($startpos, $endpos)) }
  | LPARENSPACE LAMBDA COLON expr RPAREN { ELambda([], $4, ($startpos, $endpos)) }
  // Simple cases
  | const { $1 }
  | id { $1 }

decl :
  | DEF ID LPARENNOSPACE RPAREN COLON expr { DFun($2, [], $6, ($startpos, $endpos)) }
  | DEF ID LPARENNOSPACE binds RPAREN COLON expr { DFun($2, $4, $7, ($startpos, $endpos)) }

binds :
  | bind { [$1] }
  | bind COMMA binds { $1::$3 }

bind :
  | namebind { $1 }
  | blankbind { $1 }
  | LPARENNOSPACE binds RPAREN { BTuple($2, ($startpos, $endpos)) }
  | LPARENSPACE binds RPAREN { BTuple($2, ($startpos, $endpos)) }

blankbind :
  | UNDERSCORE %prec SEMI { BBlank(($startpos, $endpos)) }

namebind :
  | ID %prec SEMI { BName($1, false, ($startpos, $endpos)) }
  | SHADOW ID %prec SEMI { BName($2, true, ($startpos, $endpos)) }

declgroup :
  | decl { [$1] }
  | decl ANDDEF declgroup { $1::$3 }

decls :
  | { [] }
  | declgroup decls { $1::$2 }


program :
  | decls expr EOF { Program($1, $2, ($startpos, $endpos)) }

%%
