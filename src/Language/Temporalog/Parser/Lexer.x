{
{-# LANGUAGE DeriveFunctor #-}
module Language.Temporalog.Parser.Lexer where

import Prelude
import Protolude (Text, bimap)

import           Data.Text.Lazy.Encoding (decodeUtf8)
import           Data.Text.Lazy (toStrict)
import qualified Data.ByteString.Lazy.Char8 as BS

import           Language.Vanillalog.Generic.Error (Error(..), Severity(..))
import           Language.Vanillalog.Generic.Parser.SrcLoc hiding (file)
import qualified Language.Vanillalog.Generic.Parser.Lexeme as L
import qualified Language.Vanillalog.Generic.Logger as Log
}

%wrapper "monadUserState-bytestring"

@idChar   = [a-zA-Z0-9_']
@var      = [A-Z]@idChar*
@fxSym    = [a-z]@idChar*

@int = [1-9][0-9]+

-- Start codes
-- scB = Body
-- scD = Declaration
-- scA = Atom
-- str = String
token :-

<0,scB,scA,scD> $white+  ;
<0>             "%".*    ;

<0,scB> "("  { basic TLeftPar }
<0,scB> ")"  { basic TRightPar }
<scA>   ","  { basic TComma }

<scB> ","        { basic TConj }
<scB> ";"        { basic TDisj }
<scB> "!"        { basic TNeg }

-- Temporal operators
<scB> "["        { basic TLeftBracket }
<scB> "]"        { basic TRightBracket }
<scB> "!"        { basic TNeg }
<scB> "EX"       { basic TEX }
<scB> "EF"       { basic TEF }
<scB> "EG"       { basic TEG }
<scB> "E"        { basic TE }
<scB> "AX"       { basic TAX }
<scB> "AF"       { basic TAF }
<scB> "AG"       { basic TAG }
<scB> "A"        { basic TA }
<scB> "U"        { basic TU }
<scB,scD> "@"    { basic TAt }

<0>         ":-"     { basic TRule  `andEnterStartCode` scB }
<0>         "?-"     { basic TQuery `andEnterStartCode` scB }
<0>         ".decl"  { basic TDecl  `andEnterStartCode` scD }
<0,scB,scD> "."      { exitStartCodeAnd $ basic TDot }

<0,scB>   @fxSym { useInput TFxSym `andEnterStartCode` scA }
<scD>     @fxSym { useInput TFxSym }
<scA>     "("    { basic TLeftPar }
<scA>     ")"    { exitStartCodeAnd $ basic TRightPar }
<scA>     true   { basic (TBool True) }
<scA>     false  { basic (TBool False) }
<scA>     @var   { useInput TVariable }
<scA,scD> @int   { useInput (TInt . read . BS.unpack) }

<scA> \"         { enterStartCode str }
<str> [^\"]+     { useInput TStr }
<str> \"         { exitStartCode }

{
data Token str =
    TLeftPar
  | TRightPar
  | TLeftBracket
  | TRightBracket
  | TDot
  | TComma
  | TRule
  | TQuery
  | TDecl
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
  | TAt
  | TFxSym    { _str  :: str }
  | TVariable { _str  :: str }
  | TStr      { _str  :: str }
  | TInt      { _int  :: Int }
  | TBool     { _bool :: Bool }
  | TEOF
  deriving (Eq, Show, Functor)

basic :: Token str -> AlexAction (L.Lexeme (Token str))
basic = useInput . const

useInput :: (BS.ByteString -> Token str) -> AlexAction (L.Lexeme (Token str))
useInput f (aPos,_,inp,_) len = do
  file <- getFile
  return $ L.Lexeme (alexToSpan aPos file len) (f $ BS.take len inp)

-- Assumes all tokens are on the same line
alexToSpan :: AlexPosn -> FilePath -> Int64 -> SrcSpan
alexToSpan (AlexPn _ line col) file len =
  SrcSpan (SrcLoc file line col)
          (SrcLoc file line (col + (fromIntegral len) - 1))

eof :: L.Lexeme (Token str)
eof = L.Lexeme dummySpan TEOF

alexEOF :: Alex (L.Lexeme (Token str))
alexEOF = return eof

data AlexUserState = AlexUserState
  { file :: FilePath
  , startCodeStack :: [ Int ]
  }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState { file = "", startCodeStack = [] }

getUserState :: Alex AlexUserState
getUserState = Alex $ \s -> Right (s, alex_ust $ s)

modifyUserState :: (AlexUserState -> AlexUserState) -> Alex ()
modifyUserState f =
  Alex $ \s -> Right (s {alex_ust = f (alex_ust s)}, ())

setUserState :: AlexUserState -> Alex ()
setUserState = modifyUserState . const

getFile :: Alex FilePath
getFile = file <$> getUserState

setFile :: FilePath -> Alex ()
setFile file = modifyUserState (\s -> s {file = file})

pushStartCode :: Int -> Alex ()
pushStartCode startCode =
  modifyUserState (\s -> s {startCodeStack = startCode : startCodeStack s})

topStartCode :: Alex Int
topStartCode = head . startCodeStack <$> getUserState

popStartCode :: Alex Int
popStartCode = do
  startCode <- topStartCode
  modifyUserState (\s -> s {startCodeStack = tail . startCodeStack $ s})
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

andEnterStartCode :: AlexAction a -> Int -> AlexAction a
andEnterStartCode action startCode input len =
  enterStartCode' startCode >> action input len

exitStartCodeAnd :: AlexAction a -> AlexAction a
exitStartCodeAnd action input len = exitStartCode' >> action input len

enterStartCode :: Int -> AlexAction (L.Lexeme (Token ByteString.ByteString))
enterStartCode = andEnterStartCode skip

exitStartCode :: AlexAction (L.Lexeme (Token ByteString.ByteString))
exitStartCode = exitStartCodeAnd skip

lex :: FilePath -> BS.ByteString -> Log.LoggerM [ L.Lexeme (Token Text) ]
lex file source =
  case result of
    Right lexemes -> pure $ fmap (fmap (toStrict . decodeUtf8)) <$> lexemes
    Left msg      -> Log.scold Nothing (fromString msg)
  where
  result = runAlex source (setFile file >> lexM)

  lexM = do
    tok <- alexMonadScan
    if tok == eof
      then return [ eof ]
      else (tok :) <$> lexM
}
