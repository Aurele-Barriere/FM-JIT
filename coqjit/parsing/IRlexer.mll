{
open Lexing
open IRparser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

let int_of_id (s:string): int =
  let si = String.sub s 3 (String.length s-3) in
  int_of_string si

let int_of_ptr (s:string): int =
    let si = String.sub s 1 (String.length s-1) in
    int_of_string si

}

let funid = "Fun"['0'-'9'] ['0'-'9']*
let verid = "Ver"['0'-'9'] ['0'-'9']*
let regid = "reg"['0'-'9'] ['0'-'9']*
let lblid = "lbl"['0'-'9'] ['0'-'9']*
let cstid = '-'? ['0'-'9'] ['0'-'9']*

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let errormsg = '\"'['a'-'z''A'-'Z'' ']*'\"' 

rule read =
  parse
  | white    { read lexbuf }
  | newline  { next_line lexbuf; read lexbuf }
  | '[' { LBRACK }
  | ']' { RBRACK }
  | '(' { LPAR }
  | ')' { RPAR }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | ':' { COLON }
  | '.' { DOT }
  | ',' { COMMA }
  | "Function" { FUNCTION }
  | "Version" { VERSION }
  | "Parameters" { PARAMS }
  | "Entry" { ENTRY }
  | "Main" { MAIN }
  | '<' { LL }
  | '>' { RR }
  | "<-" { ARROW }
  | "Plus" { PLUS }
  | "Minus" { MINUS }
  | "Mult" { MULT }
  | "Lt" { LT }
  | "Eq" { EQ }
  | "Mod" { MOD }
  | "Uminus" { UMINUS }
  | "EqZero" { EQZERO }
  | "Uplus" { UPLUS }
  | "Umult" { UMULT }
  | "Nop" { NOP }
  | "Call" { CALL }
  | "Return" { IRETURN }
  | "Cond" { COND }
  | "Print" { PRINT }
  | "Assume" { ASSUME }
  | "MemSet" { MEMSET }
  | "MemGet" { MEMGET }
  | "EndVersion" { ENDVER }
  | "EndFunction" { ENDFUNC }
  | "EndProgram" { ENDPROG }
  | funid { FID (int_of_id (Lexing.lexeme lexbuf)) }
  | regid { REG (int_of_id (Lexing.lexeme lexbuf)) }
  | lblid { LBL (int_of_id (Lexing.lexeme lexbuf)) }
  | cstid { CSTI (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }
