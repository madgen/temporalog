{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Transformation.Temporal.CTL (eliminateTemporal) where

import Protolude

import Control.Arrow ((>>>))

import Data.Functor.Foldable (Base, cata, embed)

import qualified Language.Vanillalog.AST as A
import           Language.Vanillalog.Generic.Transformation.Util (Algebra, transformBody)
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Parser.SrcLoc (span)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

eliminateTemporal :: MD.Metadata
                  -> AG.Program Void HOp (BOp 'Temporal)
                  -> Log.LoggerM (AG.Program Void (Const Void) (BOp 'ATemporal))
eliminateTemporal metadata = round1 >>> round2 >>> round3 metadata

round1 :: AG.Program Void HOp (BOp 'Temporal)
       -> AG.Program Void HOp (BOp 'Temporal)
round1 = transformBody (cata alg)
  where
  alg :: Algebra (Base (Subgoal (BOp 'Temporal) Term))
                 (Subgoal (BOp 'Temporal) Term)
  alg (SAXF span timePredSym child) = SNeg span $ SEX span timePredSym $ SNeg span child
  alg (SAGF span timePredSym child) = SNeg span $ SEF span timePredSym $ SNeg span child
  alg (SAFF span timePredSym child) = SNeg span $ SEG span timePredSym $ SNeg span child
  alg (SAUF span timePredSym child1 child2) =
    SConj span (SEU span timePredSym (SNeg span child2)
                                     (SConj span (SNeg span child1) (SNeg span child2)))
               (SNeg span $ SEG span timePredSym $ SNeg span child2)
  alg s = embed s

round2 :: AG.Program Void HOp (BOp 'Temporal)
       -> AG.Program Void HOp (BOp 'Temporal)
round2 = transformBody (cata alg)
  where
  alg :: Algebra (Base (Subgoal (BOp 'Temporal) Term))
                 (Subgoal (BOp 'Temporal) Term)
  alg (SEFF span timePredSym child) = SEU span timePredSym (SDogru span) child
  alg s = embed s

round3 :: MD.Metadata
       -> AG.Program Void HOp (BOp 'Temporal)
       -> Log.LoggerM (AG.Program Void (Const Void) (BOp 'ATemporal))
round3 = _
