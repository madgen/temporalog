{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Stage
  ( lex
  , parse
  , metadata
  , timeParameter
  , typeChecked
  , noDeclaration
  , namedQueries
  , noTemporal
  , normalised
  , compiled
  ) where

import Protolude

import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Language.Exalog.Core as E
import qualified Language.Exalog.Relation as R

import qualified Language.Vanillalog.AST as VA
import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Compiler (compile)
import qualified Language.Vanillalog.Generic.Logger as Log
import qualified Language.Vanillalog.Generic.Parser.Lexeme as L
import           Language.Vanillalog.Generic.RangeRestriction (checkRangeRestriction)
import           Language.Vanillalog.Generic.Transformation.Query (nameQueries)
import           Language.Vanillalog.Transformation.Normaliser (normalise)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD
import qualified Language.Temporalog.Parser.Lexer as Lexer
import qualified Language.Temporalog.Parser.Parser as Parser
import           Language.Temporalog.Transformation.Declaration (removeDecls)
import           Language.Temporalog.Transformation.Temporal.CTL (eliminateTemporal)
import           Language.Temporalog.Transformation.Temporal.Hybrid (eliminateAt)
import           Language.Temporalog.Transformation.TimeParameter (extendWithTime)
import           Language.Temporalog.TypeChecker (typeCheck)

type Stage a = FilePath -> BS.ByteString -> Log.LoggerM a

lex :: Stage [ L.Lexeme (Lexer.Token Text) ]
lex = Lexer.lex

parse :: Stage Program
parse = Parser.programParser

metadata :: Stage (MD.Metadata, Program)
metadata file bs = do
  ast <- parse file bs
  meta <- MD.processMetadata ast
  pure (meta, ast)

noDeclaration :: Stage (MD.Metadata, AG.Program Void HOp (BOp AtOn))
noDeclaration file bs = second removeDecls <$> metadata file bs

timeParameter :: Stage (MD.Metadata, AG.Program Void HOp (BOp AtOn))
timeParameter file bs = do
  (meta, ast) <- noDeclaration file bs
  ast' <- extendWithTime meta ast
  pure (meta, ast')

atRemoved :: Stage (MD.Metadata, AG.Program Void (Const Void) (BOp AtOff))
atRemoved file bs = do
  (meta, ast) <- timeParameter file bs
  ast' <- eliminateAt meta ast
  pure (meta, ast')

rangeRestricted :: Stage (MD.Metadata, AG.Program Void (Const Void) (BOp AtOff))
rangeRestricted file bs = do
  res@(meta, ast) <- atRemoved file bs
  checkRangeRestriction ast
  pure res

typeChecked :: Stage (MD.Metadata, AG.Program Void (Const Void) (BOp AtOff))
typeChecked file bs = do
  res <- rangeRestricted file bs
  uncurry typeCheck res
  pure res

namedQueries :: Stage (MD.Metadata, AG.Program Void (Const Void) (BOp AtOff))
namedQueries file bs = do
  (meta, ast) <- typeChecked file bs
  ast' <- nameQueries ast
  pure (meta, ast')

noTemporal :: Stage VA.Program
noTemporal file bs = do
  (meta, ast) <- namedQueries file bs
  eliminateTemporal ast

normalised :: Stage VA.Program
normalised file = noTemporal file >=> normalise

compiled :: Stage (E.Program 'E.ABase, R.Solution 'E.ABase)
compiled file = normalised file >=> compile
