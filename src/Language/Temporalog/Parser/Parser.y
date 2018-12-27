{
module Language.Temporalog.Parser.Parser where

import Prelude hiding (lex, span)
import Protolude (Text, bimap, pure)

import Control.Monad ((>=>))

import qualified Language.Vanillalog.Generic.AST as G
import qualified Language.Vanillalog.Generic.Logger as Log
import qualified Language.Vanillalog.Generic.Parser.Lexeme as L
import           Language.Vanillalog.Generic.Parser.SrcLoc

import Language.Temporalog.AST
import Language.Temporalog.Parser.Lexer (Token(..), lex)
}

%name      programParser1 PROGRAM
%name      clauseFactParser1 CLAUSE
%monad     { Log.LoggerM }
%tokentype { L.Lexeme (Token Text) }
%error     { parseError }

%token
  "("      { L.Lexeme{L._token = TLeftPar} }
  ")"      { L.Lexeme{L._token = TRightPar} }
  "["      { L.Lexeme{L._token = TLeftBracket} }
  "]"      { L.Lexeme{L._token = TRightBracket} }
  "."      { L.Lexeme{L._token = TDot} }
  ","      { L.Lexeme{L._token = TComma} }
  ":-"     { L.Lexeme{L._token = TRule} }
  "?-"     { L.Lexeme{L._token = TQuery} }

  conj     { L.Lexeme{L._token = TConj} }
  disj     { L.Lexeme{L._token = TDisj} }
  neg      { L.Lexeme{L._token = TNeg} }

  decl     { L.Lexeme{L._token = TDecl} }

  ex       { L.Lexeme{L._token = TEX} }
  ef       { L.Lexeme{L._token = TEF} }
  eg       { L.Lexeme{L._token = TEG} }
  e        { L.Lexeme{L._token = TE} }
  ax       { L.Lexeme{L._token = TAX} }
  af       { L.Lexeme{L._token = TAF} }
  ag       { L.Lexeme{L._token = TAG} }
  a        { L.Lexeme{L._token = TA} }
  u        { L.Lexeme{L._token = TU} }
  "@"      { L.Lexeme{L._token = TAt} }

  fxSym    { L.Lexeme{L._token = TFxSym{}} }
  var      { L.Lexeme{L._token = TVariable{}} }
  str      { L.Lexeme{L._token = TStr{}} }
  int      { L.Lexeme{L._token = TInt{}} }
  bool     { L.Lexeme{L._token = TBool{}} }
  eof      { L.Lexeme{L._token = TEOF} }

%left u
%left disj
%left conj
%left neg ex ef eg ax af ag

%%

PROGRAM :: { Program }
: CLAUSES eof { G.Program (span $1) . reverse $ $1 }

CLAUSES :: { [ Statement ] }
: CLAUSES DECLARATION { G.StDeclaration (span $2) $2 : $1 }
| CLAUSES CLAUSE      { G.StSentence    (span $2) $2 : $1 }
|                     { [] }

DECLARATION :: { Declaration }
: decl fxSym int "."
  { Declaration (span ($1,$4))
                (_str . L._token $ $2)
                (_int . L._token $ $3)
                Nothing }
| decl fxSym int "@" fxSym "."
  { Declaration (span ($1,$6))
                (_str . L._token $ $2)
                (_int . L._token $ $3)
                (Just $ _str . L._token $ $2) }

CLAUSE :: { Sentence }
: ATOMIC_FORMULA ":-" SUBGOAL "." { let s = span ($1,$2) in G.SClause s $ G.Clause s $1 $3 }
| ATOMIC_FORMULA "."              { let s = span ($1,$2) in G.SFact   s $ G.Fact   s $1 }
| "?-" SUBGOAL "."                { let s = span ($1,$3) in G.SQuery  s $ G.Query  s Nothing $2 }

SUBGOAL :: { Subgoal }
: ATOMIC_FORMULA              { SAtom (span $1) $1 }
| neg SUBGOAL                 { SNeg (span ($1,$2)) $2 }
| "(" SUBGOAL ")"             { $2 }
| SUBGOAL conj SUBGOAL        { SConj (span ($1,$3)) $1 $3 }
| SUBGOAL disj SUBGOAL        { SDisj (span ($1,$3)) $1 $3 }
| ex SUBGOAL                  { SEX (span ($1,$2)) $2 }
| ef SUBGOAL                  { SEF (span ($1,$2)) $2 }
| eg SUBGOAL                  { SEG (span ($1,$2)) $2 }
| e "[" SUBGOAL u SUBGOAL "]" { SEU (span ($1,$6)) $3 $5 }
| ax SUBGOAL                  { SAX (span ($1,$2)) $2 }
| af SUBGOAL                  { SAF (span ($1,$2)) $2 }
| ag SUBGOAL                  { SAG (span ($1,$2)) $2 }
| a "[" SUBGOAL u SUBGOAL "]" { SAU (span ($1,$6)) $3 $5 }

ATOMIC_FORMULA :: { AtomicFormula }
: fxSym "(" TERMS ")" { AtomicFormula (span $1) (_str . L._token $ $1) (reverse $3) }
| fxSym               { AtomicFormula (span $1) (_str . L._token $ $1) [] }

TERMS :: { [ Term ] }
: TERMS "," TERM { $3 : $1 }
| TERM           { [ $1 ] }

TERM :: { Term }
: VAR  { uncurry TVar $1 }
| SYM  { uncurry TSym $1 }

SYM :: { (SrcSpan, Sym) }
: str  { (span $1, SymText . _str  . L._token $ $1) }
| int  { (span $1, SymInt  . _int  . L._token $ $1) }
| bool { (span $1, SymBool . _bool . L._token $ $1) }

VAR :: { (SrcSpan, Var) }
: var { (span $1, Var . _str . L._token $ $1) }

{
parseError :: [ L.Lexeme (Token Text) ] -> Log.LoggerM a
parseError tokens = Log.scold (Just . span . head $ tokens) ("Parse error.")

programParser    file = lex file >=> programParser1
clauseFactParser file = lex file >=> clauseFactParser1
}
