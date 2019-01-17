{-# LANGUAGE RecordWildCards #-}

module Main where

import Protolude

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Text as T

import           Language.Exalog.Pretty ()
import qualified Language.Exalog.Solver as S

import Options.Applicative

import Language.Vanillalog.Generic.Pretty (pp)

import Language.Vanillalog.Generic.CLI.Arguments
import Language.Vanillalog.Generic.CLI.Util

import qualified Language.Temporalog.Stage as Stage

import Language.Temporalog.AST (Program)

data Stage =
    TemporalLex
  | TemporalParse
  | TemporalMeta
  | TemporalExplicit
  | TemporalType
  | TemporalNoDecl
  | TemporalNoTime
  | VanillaNormal
  | Exalog

stageParser :: Parser Stage
stageParser =
     stageFlag' TemporalLex      "lex"           "Tokenize"
 <|> stageFlag' TemporalParse    "parse"         "Parse"
 <|> stageFlag' TemporalMeta     "metadata"      "Dump metadata"
 <|> stageFlag' TemporalExplicit "explicit-time" "Extend atoms with time parameter"
 <|> stageFlag' TemporalType     "typecheck"     "Type check"
 <|> stageFlag' TemporalNoDecl   "nodecl"        "Normalise using declarations"
 <|> stageFlag' TemporalNoTime   "notime"        "Eliminate temporal ops"
 <|> stageFlag' VanillaNormal    "normal"        "Normalise"
 <|> stageFlag' Exalog           "exalog"        "Compiled Exalog program"

run :: RunOptions -> IO ()
run RunOptions{..} = do
  bs <- BS.fromStrict . encodeUtf8 <$> readFile file
  succeedOrDie (Stage.compiled file) bs $
    \(exalogProgram, initEDB) -> do
      finalEDB <- S.solve exalogProgram initEDB
      putStrLn $ pp finalEDB

repl :: ReplOptions -> IO ()
repl opts = panic "REPL is not yet supported."

prettyPrint :: PPOptions Stage -> IO ()
prettyPrint PPOptions{..} = do
  bs <- BS.fromStrict . encodeUtf8 <$> readFile file
  case stage of
    TemporalLex      -> succeedOrDie (Stage.lex file) bs print
    TemporalParse    -> succeedOrDie (Stage.parse file) bs $ putStrLn . pp
    TemporalMeta     -> succeedOrDie (fmap fst <$> Stage.metadata file) bs $
      putStrLn . pp
    TemporalExplicit -> succeedOrDie (fmap snd <$> Stage.timeParameter file) bs $
      putStrLn . pp
    TemporalType     -> succeedOrDie (Stage.typeChecked file) bs $ void . pure
    TemporalNoDecl   -> succeedOrDie (fmap snd <$> Stage.noDeclaration file) bs $
      putStrLn . pp
    TemporalNoTime   -> succeedOrDie (Stage.noTemporal file) bs $ putStrLn . pp
    VanillaNormal    -> succeedOrDie (Stage.normalised file) bs $ putStrLn . pp
    Exalog           -> succeedOrDie (Stage.compiled file) bs $
      \(exalogProgram, initEDB) -> do
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
