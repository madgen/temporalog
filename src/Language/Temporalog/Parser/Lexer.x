{
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DuplicateRecordFields #-}
module Language.Temporalog.Parser.Lexer where

import Prelude
import Protolude (Text)

import           Data.Text.Lazy.Encoding (decodeUtf8)
import           Data.Text.Lazy (toStrict)
import qualified Data.ByteString.Lazy.Char8 as BS

import           Language.Exalog.SrcLoc hiding (_file)
import qualified Language.Exalog.Logger as Log

import qualified Language.Vanillalog.Generic.Parser.Lexeme as L

#ifdef DEBUG
import Debug.Trace
#endif
}

%wrapper "monadUserState-bytestring"

@idChar   = [a-zA-Z0-9_']
@var      = [A-Z]@idChar*
@wild     = _@var?
@fxSym    = [a-z]@idChar*

@posint = [1-9][0-9]*
@int    = 0|\-?@posint

-- Start codes
-- scB  = Body
-- scSP = Single predicate
-- scBJ = Body jump
-- scBB = Body bind
-- scDP = Predicate declaration
-- scDJ = Join declaration
-- scDT = Declaration time
-- scA  = Atom
-- scDA = Declaration atom
-- str  = String
token :-

<0,scB,scSP,scBJ,scBB,scDP,scDJ,scDT,scA,scDA> $white+  ;
<0> "%".*    ;

<0,scB>    "("  { basic TLeftPar }
<0,scB>    ")"  { basic TRightPar }
<scA,scDA> ","  { basic TComma }

<scB> ","        { basic TConj }
<scB> ";"        { basic TDisj }
<scB> "!"        { basic TNeg }

-- Temporal operators
<scB> "["        { basic TLeftBracket }
<scB> "]"        { basic TRightBracket }
<scB> "EX"       { basic TEX }
<scB> "EF"       { basic TEF }
<scB> "EG"       { basic TEG }
<scB> "E"        { basic TE }
<scB> "AX"       { basic TAX }
<scB> "AF"       { basic TAF }
<scB> "AG"       { basic TAG }
<scB> "A"        { basic TA }
<scB> "U"        { basic TU }

-- When time is explicit
<scB,scBB,scBJ> "<" { enterStartCodeAnd scSP $ basic TLeftAngle }
<scSP> @fxSym       { useInput TFxSym }
<scSP> ">"          { exitStartCodeAnd $ basic TRightAngle }

<scB>           ":-" { basic TRule }
<scA>           ":-" { exitStartCodeAnd $ basic TRule }
<0>             "?-" { enterStartCodeAnd scB $ basic TQuery }
<scB,scDP,scDJ> "."  { exitStartCodeAnd $ basic TDot }
<scDT>          "."  { exitStartCodeAnd $ exitStartCodeAnd $ basic TDot }

<0>        @fxSym { enterStartCodeAnd scB $ enterStartCodeAnd scA $ useInput TFxSym }
<scB>      @fxSym { enterStartCodeAnd scA $ useInput TFxSym }
<scA,scDA> "("    { basic TLeftPar }
<scA,scDA> ")"    { exitStartCodeAnd $ basic TRightPar }
<scA>      true   { basic (TBool True) }
<scA>      false  { basic (TBool False) }
<scA>      @var   { useInput TVariable }
<scA>      @wild  { basic TWildcard }
<scA>      @int   { useInput (TInt . read . BS.unpack) }

<0>    ".pred" { enterStartCodeAnd scDP $ basic TDeclPred }
<scDP> @fxSym  { enterStartCodeAnd scDA $ useInput TFxSym }
<scDA> "int"   { basic TTTInt }
<scDA> "bool"  { basic TTTBool }
<scDA> "text"  { basic TTTText }

<0>    ".join" { enterStartCodeAnd scDJ $ basic TDeclJoin }
<scDJ> @fxSym  { useInput TFxSym }

<scDP> "@"    { enterStartCodeAnd scDT $ basic TJump }
<scDT> @fxSym { useInput TFxSym }

<scB> "|"     { enterStartCodeAnd scBB $ basic TBind }
<scBB> @var   { exitStartCodeAnd $ useInput TVariable }

<scB> "@"     { enterStartCodeAnd scBJ $ basic TJump }
<scBJ> true   { exitStartCodeAnd $ basic (TBool True) }
<scBJ> false  { exitStartCodeAnd $ basic (TBool False) }
<scBJ> @var   { exitStartCodeAnd $ useInput TVariable }
<scBJ> @wild  { exitStartCodeAnd $ basic TWildcard }
<scBJ> @int   { exitStartCodeAnd $ useInput (TInt . read . BS.unpack) }
<scBJ> \"     { exitStartCodeAnd $ enterStartCodeAnd str $ skip }

<scA> \"\"   { basic (TStr "") } -- Empty string
<scA> \"     { enterStartCodeAnd str $ skip }
<str> [^\"]+ { useInput TStr }
<str> \"     { exitStartCodeAnd skip }

{
data Token str =
    TLeftPar
  | TRightPar
  | TLeftBracket
  | TRightBracket
  | TLeftAngle
  | TRightAngle
  | TDot
  | TComma
  | TRule
  | TQuery
  | TDeclPred
  | TDeclJoin
  | TWith
  | TTTInt
  | TTTBool
  | TTTText
  | TConj
  | TDisj
  | TNeg
  | TEX
  | TEF
  | TEG
  | TE
  | TAX
  | TAF
  | TAG
  | TA
  | TU
  | TJump
  | TBind
  | TFxSym    { _tStr  :: str }
  | TVariable { _tStr  :: str }
  | TWildcard
  | TStr      { _tStr  :: str }
  | TInt      { _tInt  :: Int }
  | TBool     { _tBool :: Bool }
  | TEOF
  deriving (Eq, Show, Functor)

basic :: Token str -> AlexAction (L.Lexeme (Token str))
basic = useInput . const

useInput :: (BS.ByteString -> Token str) -> AlexAction (L.Lexeme (Token str))
useInput f (aPos,_,inp,_) len = do
  filepath <- getFile
  return $ L.Lexeme (alexToSpan aPos filepath len) (f $ BS.take len inp)

-- Assumes all tokens are on the same line
alexToSpan :: AlexPosn -> FilePath -> Int64 -> SrcSpan
alexToSpan (AlexPn _ line col) filepath len =
  SrcSpan (SrcLoc filepath line col)
          (SrcLoc filepath line (col + (fromIntegral len) - 1))

eof :: L.Lexeme (Token str)
eof = L.Lexeme dummySpan TEOF

alexEOF :: Alex (L.Lexeme (Token str))
alexEOF = return eof

data AlexUserState = AlexUserState
  { _file :: FilePath
  , _startCodeStack :: [ Int ]
  }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState { _file = "", _startCodeStack = [] }

getUserState :: Alex AlexUserState
getUserState = Alex $ \s -> Right (s, alex_ust $ s)

modifyUserState :: (AlexUserState -> AlexUserState) -> Alex ()
modifyUserState f =
  Alex $ \s -> Right (s {alex_ust = f (alex_ust s)}, ())

setUserState :: AlexUserState -> Alex ()
setUserState = modifyUserState . const

getFile :: Alex FilePath
getFile = _file <$> getUserState

setFile :: FilePath -> Alex ()
setFile filepath = modifyUserState (\s -> s {_file = filepath})

pushStartCode :: Int -> Alex ()
pushStartCode startCode =
  modifyUserState (\s -> s {_startCodeStack = startCode : _startCodeStack s})

topStartCode :: Alex Int
topStartCode = do
  stack <- _startCodeStack <$> getUserState
  case stack of
    (x:_) -> return x
    _     -> Alex . const $
      Left "Impossible: The lexer start code stack is empty."

popStartCode :: Alex Int
popStartCode = do
  startCode <- topStartCode
  modifyUserState (\s -> s {_startCodeStack = tail . _startCodeStack $ s})
  pure startCode

enterStartCode' :: Int -> Alex ()
enterStartCode' newStartCode = do
  currentStartCode <- alexGetStartCode
  pushStartCode currentStartCode
  alexSetStartCode newStartCode

exitStartCode' :: Alex ()
exitStartCode' = do
  startCodeToReturn <- popStartCode
  alexSetStartCode startCodeToReturn

enterStartCodeAnd :: Int -> AlexAction a -> AlexAction a
enterStartCodeAnd startCode action inp len =
  enterStartCode' startCode *> action inp len

exitStartCodeAnd :: AlexAction a -> AlexAction a
exitStartCodeAnd action inp len = exitStartCode' *> action inp len

lex :: FilePath -> BS.ByteString -> Log.Logger [ L.Lexeme (Token Text) ]
lex filepath source =
  case result of
    Right lexemes -> pure $ fmap (fmap (toStrict . decodeUtf8)) <$> lexemes
    Left msg      -> Log.scold Nothing (fromString msg)
  where
  result = runAlex source (setFile filepath >> lexM)

  lexM = do
    tok <- alexMonadScan

#if defined (DEBUG) && defined (LEXER)
    traceShowM tok
    debugStartCodeStack
    debugStartCode
#endif

    if tok == eof
      then return [ eof ]
      else (tok :) <$> lexM

#if defined (DEBUG) && defined (LEXER)
debugStartCodeStack = do
  stack <- fmap StartCode . _startCodeStack <$> getUserState
  traceM $ "Start code stack: " <> show stack

debugStartCode = do
  startCode <- alexGetStartCode
  traceM $ "Active start code: " <> show (StartCode startCode)

newtype StartCode = StartCode Int

instance Show StartCode where
  show (StartCode i) =
    if i == 0         then "0"
    else if i == scA  then "atom"
    else if i == scB  then "body"
    else if i == scBT then "body time"
    else if i == scD  then "decl"
    else if i == scDT then "decl time"
    else if i == scDA then "decl atom"
    else if i == str  then "string"
    else error "Unknown start code"
#endif
}
