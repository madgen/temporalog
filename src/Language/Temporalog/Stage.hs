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
  , guardInjected
  , dataflowSafe
  ) where

import Protolude

import qualified Data.ByteString.Lazy.Char8 as BS

import qualified Language.Exalog.Core as E
import qualified Language.Exalog.Logger as Log
import qualified Language.Exalog.Relation as R
import           Language.Exalog.RangeRestriction (checkRangeRestriction)
import           Language.Exalog.WellModing (checkWellModedness)

import qualified Language.Vanillalog.AST as VA
import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Compiler (compile)
import qualified Language.Vanillalog.Generic.Parser.Lexeme as L
import           Language.Vanillalog.Generic.Transformation.Query (nameQueries)
import           Language.Vanillalog.Transformation.Normaliser (normalise)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD
import qualified Language.Temporalog.Parser.Lexer as Lexer
import qualified Language.Temporalog.Parser.Parser as Parser
import           Language.Temporalog.Transformation.Declaration (removeDecls, checkDecls, checkJoins)
import           Language.Temporalog.Transformation.GuardInjection (injectGuards)
import           Language.Temporalog.Transformation.Temporal.Compiler (eliminateTemporal)
import           Language.Temporalog.Transformation.Temporal.Elaborator (elaborate)
import           Language.Temporalog.Transformation.Temporal.Identities (applyTemporalIdentities)
import           Language.Temporalog.Transformation.Temporal.JoinInjection (injectJoins)
import           Language.Temporalog.Transformation.Temporal.Vanilla (toVanilla)
import           Language.Temporalog.TypeChecker (typeCheck)

type Stage a = FilePath -> BS.ByteString -> Log.Logger a

lex :: Stage [ L.Lexeme (Lexer.Token Text) ]
lex = Lexer.lex

parse :: Stage (Program 'Implicit)
parse = Parser.programParser

metadata :: Stage (MD.Metadata, Program 'Implicit)
metadata file bs = do
  ast <- parse file bs
  checkDecls (AG.sentences ast) (AG.declarations ast)
  meta <- MD.processMetadata (predicateDeclarations ast)
  pure (meta, ast)

elaborated :: Stage (MD.Metadata, Program 'Explicit)
elaborated file bs = do
  (meta, ast) <- metadata file bs
  ast'        <- elaborate meta ast
  pure (meta, ast')

joinInjected :: Stage (MD.Metadata, Program 'Explicit)
joinInjected file bs = do
  (meta, ast) <- elaborated file bs
  let ast'     = injectJoins _ meta ast
  pure (meta, ast')

noDeclaration :: Stage (MD.Metadata, AG.Program Void (HOp 'Explicit) (BOp 'Explicit 'Temporal))
noDeclaration file bs = second removeDecls <$> joinInjected file bs

noTemporal :: Stage (MD.Metadata, AG.Program Void (Const Void) (BOp 'Explicit 'ATemporal))
noTemporal file bs = do
  (meta, ast) <- noDeclaration file bs
  eliminateTemporal meta (applyTemporalIdentities ast)

vanilla :: Stage (MD.Metadata, VA.Program)
vanilla file bs = do
  (meta, ast) <- noTemporal file bs
  ast' <- toVanilla ast
  pure (meta, ast')

typeChecked :: Stage (MD.Metadata, VA.Program)
typeChecked file bs = do
  res <- vanilla file bs
  uncurry typeCheck res
  pure res

namedQueries :: Stage (MD.Metadata, VA.Program)
namedQueries file bs = do
  (meta, ast) <- typeChecked file bs
  ast' <- nameQueries ast
  pure (meta, ast')

normalised :: Stage (MD.Metadata, VA.Program)
normalised file bs = do
  (meta, ast) <- namedQueries file bs
  ast' <- normalise ast
  pure (meta, ast')

compiled :: Stage (MD.Metadata, (E.Program 'E.ABase, R.Solution 'E.ABase))
compiled file bs = do
  (meta, ast) <- normalised file bs
  res         <- compile ast

  pure (meta, res)

guardInjected :: Stage (E.Program 'E.ABase, R.Solution 'E.ABase)
guardInjected file bs = do
  (meta, res) <- compiled file bs
  injectGuards meta res

dataflowSafe :: Stage (E.Program 'E.ABase, R.Solution 'E.ABase)
dataflowSafe file bs = do
  res@(pr, _) <- guardInjected file bs
  checkRangeRestriction pr
  checkWellModedness pr

  pure res
