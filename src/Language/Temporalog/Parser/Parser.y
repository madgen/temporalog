{
{-# LANGUAGE DataKinds #-}

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
  intType  { L.Lexeme{L._token = TTTInt} }
  boolType { L.Lexeme{L._token = TTTBool} }
  textType { L.Lexeme{L._token = TTTText} }

  ex       { L.Lexeme{L._token = TEX} }
  ef       { L.Lexeme{L._token = TEF} }
  eg       { L.Lexeme{L._token = TEG} }
  e        { L.Lexeme{L._token = TE} }
  ax       { L.Lexeme{L._token = TAX} }
  af       { L.Lexeme{L._token = TAF} }
  ag       { L.Lexeme{L._token = TAG} }
  a        { L.Lexeme{L._token = TA} }
  u        { L.Lexeme{L._token = TU} }
  "@"      { L.Lexeme{L._token = TJump} }
  "|"      { L.Lexeme{L._token = TBind} }

  fxSym    { L.Lexeme{L._token = TFxSym{}} }
  var      { L.Lexeme{L._token = TVariable{}} }
  str      { L.Lexeme{L._token = TStr{}} }
  int      { L.Lexeme{L._token = TInt{}} }
  bool     { L.Lexeme{L._token = TBool{}} }
  eof      { L.Lexeme{L._token = TEOF} }

%right "@"
%left "|"
%left u
%left disj
%left conj
%left neg ex ef eg ax af ag

%%

PROGRAM :: { Program }
: CLAUSES eof { G.Program (span $1) . reverse $ $1 }

CLAUSES :: { [ Statement ] }
: CLAUSES DECLARATION { G.StDeclaration $2 : $1 }
| CLAUSES CLAUSE      { G.StSentence    $2 : $1 }
|                     { [] }

DECLARATION :: { Declaration }
: decl ATOM_TYPE "."             { Declaration (span ($1,$3)) $2 Nothing }
| decl ATOM_TYPE "@" FX_SYMS "." { Declaration (span ($1,$5)) $2 (Just $ map snd . reverse $ $4) }

CLAUSE :: { Sentence }
: HEAD ":-" SUBGOAL "." { G.SClause $ G.Clause (span ($1,$4)) $1 $3 }
| HEAD "."              { G.SFact   $ G.Fact   (span ($1,$2)) $1 }
| "?-" SUBGOAL "."      { G.SQuery  $ G.Query  (span ($1,$3)) Nothing $2 }

HEAD :: { Subgoal HOp Term }
: ATOMIC_FORMULA        { SAtom     (span $1)      $1 }
| HEAD "@" FX_SYM TERM  { SHeadJump (span ($1,$4)) $1 (snd $3) $4 }

SUBGOAL :: { Subgoal (BOp 'Temporal) Term }
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
| SUBGOAL "@" FX_SYM TERM     { SBodyJump (span ($1,$4)) $1 (snd $3) $4 }
| "|" FX_SYM VAR SUBGOAL      { SBind     (span ($1,$4)) (snd $2) $3 $4 }

ATOMIC_FORMULA :: { AtomicFormula Term }
: FX_SYM "(" TERMS ")" { AtomicFormula (transSpan (fst $1) (span $4)) (snd $1) (reverse $3) }
| FX_SYM               { AtomicFormula (fst $1)                       (snd $1) [] }

ATOM_TYPE :: { AtomicFormula TermType }
: FX_SYM "(" TYPES ")" { AtomicFormula (transSpan (fst $1) (span $4)) (snd $1) (reverse $3) }
| FX_SYM               { AtomicFormula (fst $1)                       (snd $1) [] }

FX_SYMS :: { [ (SrcSpan, G.PredicateSymbol) ] }
: FX_SYMS FX_SYM { $2 : $1 }
| FX_SYM         { [ $1 ] }

FX_SYM :: { (SrcSpan, G.PredicateSymbol) }
: fxSym { (span $1, G.PredicateSymbol . pure . _tStr . L._token $ $1) }

TERMS :: { [ Term ] }
: TERMS "," TERM { $3 : $1 }
| TERM           { [ $1 ] }

TYPES :: { [ TermType ] }
: TYPES "," TYPE { $3 : $1 }
| TYPE           { [ $1 ] }

TERM :: { Term }
: VAR  { TVar $1 }
| SYM  { TSym $1 }

TYPE :: { TermType }
: intType  { TTInt }
| boolType { TTBool }
| textType { TTText }

SYM :: { Sym }
: str  { SymText (span $1) . _tStr  . L._token $ $1 }
| int  { SymInt  (span $1) . _tInt  . L._token $ $1 }
| bool { SymBool (span $1) . _tBool . L._token $ $1 }

VAR :: { Var }
: var { Var (span $1) . _tStr . L._token $ $1 }

{
parseError :: [ L.Lexeme (Token Text) ] -> Log.LoggerM a
parseError tokens = Log.scold (Just . span . head $ tokens) "Parse error."

programParser    file = lex file >=> programParser1
clauseFactParser file = lex file >=> clauseFactParser1
}
