{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Stage
  ( lex
  , parse
  , metadata
  , noDeclaration
  , typeChecked
  , namedQueries
  , noTemporal
  , vanilla
  , normalised
  , compiled
  ) where

import Protolude

import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Language.Exalog.Core as E
import qualified Language.Exalog.Logger as Log
import qualified Language.Exalog.Relation as R

import qualified Language.Vanillalog.AST as VA
import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Compiler (compile)
import qualified Language.Vanillalog.Generic.Parser.Lexeme as L
import           Language.Vanillalog.Generic.RangeRestriction (checkRangeRestriction)
import           Language.Vanillalog.Generic.Transformation.Query (nameQueries)
import           Language.Vanillalog.Transformation.Normaliser (normalise)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD
import qualified Language.Temporalog.Parser.Lexer as Lexer
import qualified Language.Temporalog.Parser.Parser as Parser
import           Language.Temporalog.Transformation.Declaration (removeDecls)
import           Language.Temporalog.Transformation.Temporal.Identities (applyTemporalIdentities)
import           Language.Temporalog.Transformation.Temporal.Compiler (eliminateTemporal)
import           Language.Temporalog.Transformation.Temporal.Vanilla (toVanilla)
import           Language.Temporalog.TypeChecker (typeCheck)

type Stage a = FilePath -> BS.ByteString -> Log.Logger a

lex :: Stage [ L.Lexeme (Lexer.Token Text) ]
lex = Lexer.lex

parse :: Stage Program
parse = Parser.programParser

metadata :: Stage (MD.Metadata, Program)
metadata file bs = do
  ast <- parse file bs
  meta <- MD.processMetadata ast
  pure (meta, ast)

noDeclaration :: Stage (MD.Metadata, AG.Program Void HOp (BOp 'Temporal))
noDeclaration file bs = second removeDecls <$> metadata file bs

noTemporal :: Stage (MD.Metadata, AG.Program Void (Const Void) (BOp 'ATemporal))
noTemporal file bs = do
  (meta, ast) <- noDeclaration file bs
  eliminateTemporal meta (applyTemporalIdentities ast)

vanilla :: Stage (MD.Metadata, VA.Program)
vanilla file bs = do
  (meta, ast) <- noTemporal file bs
  ast' <- toVanilla ast
  pure (meta, ast')

rangeRestricted :: Stage (MD.Metadata, VA.Program)
rangeRestricted file bs = do
  res@(meta, ast) <- vanilla file bs
  checkRangeRestriction ast
  pure res

typeChecked :: Stage VA.Program
typeChecked file bs = do
  res@(meta, ast) <- rangeRestricted file bs
  uncurry typeCheck res
  pure ast

namedQueries :: Stage VA.Program
namedQueries file = typeChecked file >=> nameQueries

normalised :: Stage VA.Program
normalised file = namedQueries file >=> normalise

compiled :: Stage (E.Program 'E.ABase, R.Solution 'E.ABase)
compiled file = normalised file >=> compile
