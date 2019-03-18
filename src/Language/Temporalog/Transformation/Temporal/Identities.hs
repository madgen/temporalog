{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Transformation.Temporal.Identities
  ( applyTemporalIdentities
  ) where

import Protolude

import Data.Functor.Foldable (Base, cata, embed)

import           Language.Vanillalog.Generic.Transformation.Util (Algebra, transformBody)
import qualified Language.Vanillalog.Generic.AST as AG

import           Language.Temporalog.AST

applyTemporalIdentities :: AG.Program Void HOp (BOp 'Temporal)
                        -> AG.Program Void HOp (BOp 'Temporal)
applyTemporalIdentities = round2 . round1

-- |Eliminate AX, AG, AU
round1 :: AG.Program Void HOp (BOp 'Temporal)
       -> AG.Program Void HOp (BOp 'Temporal)
round1 = transformBody (cata alg)
  where
  alg :: Algebra (Base (Subgoal (BOp 'Temporal) Term))
                 (Subgoal (BOp 'Temporal) Term)
  alg (SAXF span timePredSym child) = SNeg span $ SEX span timePredSym $ SNeg span child
  alg (SAGF span timePredSym child) = SNeg span $ SEF span timePredSym $ SNeg span child
  alg (SAUF span timePredSym child1 child2) =
    SConj span (SEU span timePredSym (SNeg span child2)
                                     (SConj span (SNeg span child1) (SNeg span child2)))
               (SNeg span $ SEG span timePredSym $ SNeg span child2)
  alg s = embed s

-- |Eliminate AF, EF
round2 :: AG.Program Void HOp (BOp 'Temporal)
       -> AG.Program Void HOp (BOp 'Temporal)
round2 = transformBody (cata alg)
  where
  alg :: Algebra (Base (Subgoal (BOp 'Temporal) Term))
                 (Subgoal (BOp 'Temporal) Term)
  alg (SAFF span timePredSym child) = SNeg span $ SEG span timePredSym $ SNeg span child
  alg (SEFF span timePredSym child) = SEU span timePredSym (SDogru span) child
  alg s = embed s
