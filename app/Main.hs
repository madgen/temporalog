{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Protolude

import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Language.Exalog.Core as E
import qualified Language.Exalog.Relation as R
import           Language.Exalog.Pretty ()
import qualified Language.Exalog.Solver as S

import Options.Applicative

import Language.Vanillalog.Generic.Pretty (pp)

import Language.Vanillalog.Generic.CLI.Arguments
import Language.Vanillalog.Generic.CLI.Util

import qualified Language.Temporalog.Stage as Stage

data Stage =
    TemporalLex
  | TemporalParse
  | TemporalMeta
  | TemporalElaborate
  | TemporalNoDecl
  | TemporalType
  | TemporalNoTime
  | Vanilla
  | VanillaNormal
  | Exalog
  | ExalogGuard
  | ExalogDataflow

stageParser :: Parser Stage
stageParser =
     stageFlag' TemporalLex       "lex"       "Tokenize"
 <|> stageFlag' TemporalParse     "parse"     "Parse"
 <|> stageFlag' TemporalMeta      "metadata"  "Dump metadata"
 <|> stageFlag' TemporalElaborate "elaborate" "Time elaboration"
 <|> stageFlag' TemporalNoDecl    "no-decl"   "Remove declarations"
 <|> stageFlag' TemporalNoTime    "no-time"   "Eliminate temporal ops"
 <|> stageFlag' TemporalType      "typecheck" "Type check"
 <|> stageFlag' Vanilla           "vanilla"   "Vanilla"
 <|> stageFlag' VanillaNormal     "normal"    "Normalise"
 <|> stageFlag' Exalog            "exalog"    "Compiled Exalog program"
 <|> stageFlag' ExalogGuard       "guard"     "Guard injection Exalog program"
 <|> stageFlag' ExalogDataflow    "checked"   "Well-moded and range-restricted"

run :: RunOptions -> IO ()
run RunOptions{..} = do
  bs <- BS.fromStrict . encodeUtf8 <$> readFile file
  succeedOrDie (Stage.dataflowSafe file >=> uncurry S.solve) bs $
      putStrLn . pp

repl :: ReplOptions -> IO ()
repl opts = panic "REPL is not yet supported."

prettyPrint :: PPOptions Stage -> IO ()
prettyPrint PPOptions{..} = do
  bs <- BS.fromStrict . encodeUtf8 <$> readFile file
  case stage of
    TemporalLex       -> succeedOrDie (Stage.lex file) bs print
    TemporalParse     -> succeedOrDie (Stage.parse file) bs $ putStrLn . pp
    TemporalMeta      -> succeedOrDie (fmap fst <$> Stage.metadata file) bs $
      putStrLn . pp
    TemporalElaborate -> succeedOrDie (fmap snd <$> Stage.elaborated file) bs $
      putStrLn . pp
    TemporalNoDecl    -> succeedOrDie (fmap snd <$> Stage.noDeclaration file) bs $
      putStrLn . pp
    TemporalNoTime    -> succeedOrDie (fmap snd <$> Stage.noTemporal file) bs $
      putStrLn . pp
    TemporalType      -> succeedOrDie (Stage.typeChecked file) bs $ void . pure
    Vanilla           -> succeedOrDie (fmap snd <$> Stage.vanilla file) bs $
      putStrLn . pp
    VanillaNormal     -> succeedOrDie (fmap snd <$> Stage.normalised file) bs $
      putStrLn . pp
    Exalog            -> succeedOrDie (fmap snd <$> Stage.compiled file) bs
      printExalog
    ExalogGuard       -> succeedOrDie (Stage.guardInjected file) bs
      printExalog
    ExalogDataflow    -> succeedOrDie (Stage.dataflowSafe file) bs
      printExalog

printExalog :: (E.Program 'E.ABase, R.Solution 'E.ABase) -> IO ()
printExalog (exalogProgram, initEDB) = do
  putStrLn $ pp exalogProgram
  putStrLn ("" :: Text)
  putStrLn $ pp initEDB

main :: IO ()
main = do
  command <- execParser (info (opts (ppOptions stageParser)) idm)
  case command of
    Run runOpts   -> run  runOpts
    Repl replOpts -> repl replOpts
    PrettyPrint ppOpts -> prettyPrint ppOpts
