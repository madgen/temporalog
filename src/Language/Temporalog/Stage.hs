{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Stage
  ( lex
  , parse
  , metadata
  , elaborated
  , joinInjected
  , noDeclaration
  , typeChecked
  , namedQueries
  , noTemporal
  , vanilla
  , normalised
  , compiled
  , rangeRestricted
  , wellModed
  ) where

import Protolude

import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Language.Exalog.Core as E
import qualified Language.Exalog.Logger as Log
import           Language.Exalog.RangeRestriction (fixRangeRestriction)
import qualified Language.Exalog.Relation as R
import           Language.Exalog.Renamer (rename)
import           Language.Exalog.WellModing (fixModing)

import qualified Language.Vanillalog.AST as VA
import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Compiler (compile)
import qualified Language.Vanillalog.Generic.Parser.Lexeme as L
import           Language.Vanillalog.Generic.Transformation.Query (nameQueries)
import           Language.Vanillalog.Transformation.Normaliser (normalise)

import qualified Language.Temporalog.Analysis.Metadata as MD
import           Language.Temporalog.Analysis.TypeChecker (typeCheck)
import           Language.Temporalog.AST
import qualified Language.Temporalog.Parser.Lexer as Lexer
import qualified Language.Temporalog.Parser.Parser as Parser
import           Language.Temporalog.Transformation.Declaration (removeDecls, checkDecls)
import           Language.Temporalog.Transformation.Temporal.Compiler (eliminateTemporal)
import           Language.Temporalog.Transformation.Temporal.Elaborator (elaborate)
import           Language.Temporalog.Transformation.Temporal.Identities (applyTemporalIdentities)
import           Language.Temporalog.Transformation.Temporal.JoinInjection (injectJoins)
import           Language.Temporalog.Transformation.Temporal.Vanilla (toVanilla)

type Stage a = FilePath -> BS.ByteString -> Log.Logger a

lex :: Stage [ L.Lexeme (Lexer.Token Text) ]
lex = Lexer.lex

parse :: Stage (Program 'Implicit)
parse = Parser.programParser

metadata :: Stage (MD.Metadata, Program 'Implicit)
metadata file bs = do
  ast <- parse file bs
  checkDecls (AG.sentences ast) (AG.declarations ast)
  meta <- MD.processMetadata ast
  pure (meta, ast)

elaborated :: Stage (MD.Metadata, Program 'Explicit)
elaborated file bs = do
  (meta, ast) <- metadata file bs
  ast'        <- elaborate meta ast
  pure (meta, ast')

noDeclaration :: Stage (MD.Metadata, AG.Program Void (HOp 'Explicit) (BOp 'Explicit 'Temporal))
noDeclaration file bs = second removeDecls <$> elaborated file bs

joinInjected :: Stage (MD.Metadata, AG.Program Void (HOp 'Explicit) (BOp 'Explicit 'Temporal))
joinInjected file bs = do
  (meta, ast) <- noDeclaration file bs
  ast'        <- injectJoins meta ast
  pure (meta, ast')

noTemporal :: Stage (MD.Metadata, AG.Program Void (Const Void) (BOp 'Explicit 'ATemporal))
noTemporal file bs = do
  (meta, ast) <- joinInjected file bs
  eliminateTemporal meta (applyTemporalIdentities ast)

vanilla :: Stage (MD.Metadata, VA.Program)
vanilla file bs = do
  (meta, ast) <- noTemporal file bs
  ast' <- toVanilla ast
  pure (meta, ast')

typeChecked :: Stage VA.Program
typeChecked file bs = do
  (meta, ast) <- vanilla file bs
  typeCheck meta ast
  pure ast

namedQueries :: Stage VA.Program
namedQueries file = typeChecked file >=> nameQueries

normalised :: Stage VA.Program
normalised file = namedQueries file >=> normalise

compiled :: Stage (E.Program 'E.ABase, R.Solution 'E.ABase)
compiled file = normalised file >=> compile

rangeRestricted :: Stage (E.Program 'E.ABase, R.Solution 'E.ABase)
rangeRestricted file = compiled file >=> rename >=> fixRangeRestriction

wellModed :: Stage (E.Program 'E.ABase, R.Solution 'E.ABase)
wellModed file = rangeRestricted file >=> rename >=> fixModing
