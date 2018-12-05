{-# LANGUAGE RecordWildCards #-}

module Main where

import Protolude

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Text as T

import           Language.Exalog.Pretty ()
import qualified Language.Exalog.Solver as S

import Options.Applicative

import Language.Vanillalog.Generic.Compiler (compile)
import Language.Vanillalog.Generic.Pretty (pp)
import Language.Vanillalog.Generic.Transformation.Query (nameQueries)
import Language.Vanillalog.Transformation.Normaliser (normalise)

import Language.Vanillalog.Generic.CLI.Arguments
import Language.Vanillalog.Generic.CLI.Util

import Language.Temporalog.AST (Program)
import Language.Temporalog.Transformation.TemporalEliminator (eliminateTemporal)
import Language.Temporalog.Parser.Lexer (lex)
import Language.Temporalog.Parser.Parser (programParser)

data Stage =
    TemporalLex
  | TemporalParse
  | TemporalNoTime
  | VanillaNormal
  | Exalog

stageParser :: Parser Stage
stageParser =
     stageFlag' TemporalLex    "lex"    "Tokenize"
 <|> stageFlag' TemporalParse  "parse"  "Parse"
 <|> stageFlag' TemporalNoTime "notime" "Eliminate temporal ops"
 <|> stageFlag' VanillaNormal  "normal" "Normalise"
 <|> stageFlag' Exalog         "exalog" "Compile to Exalog"

run :: RunOptions -> IO ()
run RunOptions{..} = do
  bs <- BS.fromStrict . encodeUtf8 <$> readFile file
  succeedOrDie (programParser file >=> nameQueries
                                   >=> eliminateTemporal
                                   >=> normalise
                                   >=> compile) bs $
    \(exalogProgram, initEDB) -> do
      finalEDB <- S.solve exalogProgram initEDB
      putStrLn $ pp finalEDB

repl :: ReplOptions -> IO ()
repl opts = panic "REPL is not yet supported."

prettyPrint :: PPOptions Stage -> IO ()
prettyPrint PPOptions{..} = do
  bs <- BS.fromStrict . encodeUtf8 <$> readFile file
  case stage of
    TemporalLex -> succeedOrDie (lex file) bs print
    TemporalParse -> succeedOrDie (programParser file) bs $ putStrLn . pp
    TemporalNoTime ->
      succeedOrDie (programParser file >=> nameQueries
                                       >=> eliminateTemporal) bs $
        putStrLn . pp
    VanillaNormal ->
      succeedOrDie (programParser file >=> nameQueries
                                       >=> eliminateTemporal
                                       >=> normalise) bs $
        putStrLn . pp
    Exalog ->
      succeedOrDie (programParser file >=> nameQueries
                                       >=> eliminateTemporal
                                       >=> normalise
                                       >=> compile) bs $
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
