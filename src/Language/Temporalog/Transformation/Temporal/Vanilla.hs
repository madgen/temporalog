{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.Transformation.Temporal.Vanilla (toVanilla) where

import Protolude

import Data.Functor.Foldable (Base, cata, embed)

import           Language.Temporalog.AST

import qualified Language.Exalog.Logger as Log

import qualified Language.Vanillalog.AST as A
import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Transformation.Util (Algebra)

toVanilla :: AG.Program Void (Const Void) (BOp 'ATemporal)
          -> Log.Logger A.Program
toVanilla AG.Program{..} =
  (\sts -> AG.Program{_statements = sts,..}) <$> traverse goSt _statements
  where
  goSt :: AG.Statement Void (Const Void) (BOp 'ATemporal)
       -> Log.Logger A.Statement
  goSt AG.StSentence{..} =
    (\s -> AG.StSentence{_sentence = s,..}) <$> goSent _sentence
  goSt AG.StDeclaration{..} = absurd _declaration

  goSent :: AG.Sentence (Const Void) (BOp 'ATemporal) -> Log.Logger A.Sentence
  goSent sent =
    case sent of
      AG.SFact AG.Fact{..} -> pure $ AG.SFact AG.Fact{..}
      AG.SClause AG.Clause{..} -> do
        newBody <- goBody . cleanseDogru $ _body
        pure $ AG.SClause AG.Clause {_body = newBody,..}
      AG.SQuery AG.Query{..} -> do
        newBody <- goBody . cleanseDogru $ _body
        pure $ AG.SQuery AG.Query {_body = newBody,..}

  goBody :: A.Subgoal (BOp 'ATemporal) Term
         -> Log.Logger (A.Subgoal A.Op Term)
  goBody (SAtom s atom)    = pure $ A.SAtom s atom
  goBody (SConj s phi psi) = A.SConj s <$> goBody phi <*> goBody psi
  goBody (SDisj s phi psi) = A.SDisj s <$> goBody phi <*> goBody psi
  goBody (SNeg  s phi)     = A.SNeg  s <$> goBody phi
  goBody (SDogru s)        =
    Log.scream (Just s) "True should have been eliminated by now."

cleanseDogru :: A.Subgoal (BOp 'ATemporal) Term
             -> A.Subgoal (BOp 'ATemporal) Term
cleanseDogru = cata alg
  where
  alg :: Algebra (Base (A.Subgoal (BOp 'ATemporal) Term))
                 (A.Subgoal (BOp 'ATemporal) Term)
  alg (SNegF _ (SNeg _ s))                = s
  alg (SConjF span SDogru{} s)            = s
  alg (SConjF span s SDogru{})            = s
  alg (SDisjF span s@SDogru{} _)          = s
  alg (SDisjF span _ s@SDogru{})          = s
  alg (SConjF span s@(SNeg _ SDogru{}) _) = s
  alg (SConjF span _ s@(SNeg _ SDogru{})) = s
  alg (SDisjF span (SNeg _ SDogru{}) s)   = s
  alg (SDisjF span s (SNeg _ SDogru{}))   = s
  alg s                                   = embed s
