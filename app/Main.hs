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
  | TemporalJoin
  | TemporalType
  | TemporalNoTime
  | Vanilla
  | VanillaNormal
  | Exalog
  | ExalogRangeRepair
  | ExalogModeRepair

stageParser :: Parser Stage
stageParser =
     stageFlag' TemporalLex       "lex"          "Tokenize"
 <|> stageFlag' TemporalParse     "parse"        "Parse"
 <|> stageFlag' TemporalMeta      "metadata"     "Dump metadata"
 <|> stageFlag' TemporalElaborate "elaborate"    "Time elaboration"
 <|> stageFlag' TemporalNoDecl    "no-decl"      "Remove declarations"
 <|> stageFlag' TemporalJoin      "join"         "Inject joins"
 <|> stageFlag' TemporalNoTime    "no-time"      "Eliminate temporal ops"
 <|> stageFlag' TemporalType      "typecheck"    "Type check"
 <|> stageFlag' Vanilla           "vanilla"      "Vanilla"
 <|> stageFlag' VanillaNormal     "normal"       "Normalise"
 <|> stageFlag' Exalog            "exalog"       "Compiled Exalog program"
 <|> stageFlag' ExalogRangeRepair "range-repair" "Repair and check range restriction"
 <|> stageFlag' ExalogModeRepair  "mode-repair"  "Repair and check moding"

run :: RunOptions -> IO ()
run RunOptions{..} = do
  bs <- BS.fromStrict . encodeUtf8 <$> readFile _file

  succeedOrDie (Stage.parse _file) bs $ \ast ->
    succeedOrDie (Stage.wellModed _file >=> uncurry S.solve) bs $ display ast

repl :: ReplOptions -> IO ()
repl _ = panic "REPL is not yet supported."

prettyPrint :: PPOptions Stage -> IO ()
prettyPrint PPOptions{..} = do
  bs <- BS.fromStrict . encodeUtf8 <$> readFile _file
  case _stage of
    TemporalLex       -> succeedOrDie (Stage.lex _file) bs print
    TemporalParse     -> succeedOrDie (Stage.parse _file) bs $ putStrLn . pp
    TemporalMeta      -> succeedOrDie (fmap fst <$> Stage.metadata _file) bs $
      putStrLn . pp
    TemporalElaborate -> succeedOrDie (fmap snd <$> Stage.elaborated _file) bs $
      putStrLn . pp
    TemporalNoDecl    -> succeedOrDie (fmap snd <$> Stage.noDeclaration _file) bs $
      putStrLn . pp
    TemporalJoin      -> succeedOrDie (fmap snd <$> Stage.joinInjected _file) bs $
      putStrLn . pp
    TemporalNoTime    -> succeedOrDie (fmap snd <$> Stage.noTemporal _file) bs $
      putStrLn . pp
    TemporalType      -> succeedOrDie (Stage.typeChecked _file) bs $ void . pure
    Vanilla           -> succeedOrDie (fmap snd <$> Stage.vanilla _file) bs $
      putStrLn . pp
    VanillaNormal     -> succeedOrDie (Stage.normalised _file) bs $ putStrLn . pp
    Exalog            -> succeedOrDie (Stage.compiled        _file) bs printExalog
    ExalogRangeRepair -> succeedOrDie (Stage.rangeRestricted _file) bs printExalog
    ExalogModeRepair  -> succeedOrDie (Stage.wellModed       _file) bs printExalog

printExalog :: (E.Program 'E.ABase, R.Solution 'E.ABase) -> IO ()
printExalog (exalogProgram, initEDB) = do
  putStrLn $ pp exalogProgram
  putStrLn ("" :: Text)
  putStrLn $ pp initEDB

main :: IO ()
main = do
  com <- execParser (info (opts (fromStageParser stageParser)) idm)
  case com of
    Run runOpts   -> run  runOpts
    Repl replOpts -> repl replOpts
    PrettyPrint ppOpts -> prettyPrint ppOpts
