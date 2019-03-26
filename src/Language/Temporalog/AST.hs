{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Temporalog.AST
  ( Program(..)
  , Statement(..)
  , Declaration(..)
  , Sentence(..)
  , Query(..)
  , Clause(..)
  , Fact(..)
  , Subgoal
  , pattern SAtom, pattern SNeg, pattern SConj, pattern SDisj
  , pattern SAtomF, pattern SNegF, pattern SConjF, pattern SDisjF
  , pattern SDogru, pattern SDogruF
  , pattern SEX, pattern SEF, pattern SEG, pattern SEU
  , pattern SAX, pattern SAF, pattern SAG, pattern SAU
  , pattern SHeadJump, pattern SBodyJump, pattern SBind
  , pattern SEXF, pattern SEFF, pattern SEGF, pattern SEUF
  , pattern SAXF, pattern SAFF, pattern SAGF, pattern SAUF
  , pattern SHeadJumpF, pattern SBodyJumpF, pattern SBindF
  , HOp(..), BOp(..), Temporal(..), AG.OpKind(..), AG.SomeOp(..)
  , AG.AtomicFormula(..)
  , AG.PredicateSymbol(..)
  , AG.Term(..)
  , AG.TermType(..)
  , AG.termType
  , AG.Var(..)
  , AG.Sym(..)
  , AG.vars
  , freeVars
  , AG.operation
  ) where

import Protolude hiding ((<>), empty)

import Data.Functor.Foldable (Base, cata)

import qualified Data.List.NonEmpty as NE

import qualified Language.Exalog.Core as E

import Text.PrettyPrint ((<+>), (<>), int, empty, punctuate, hcat)

import           Language.Exalog.Pretty.Helper ((<+?>), prettyC)

import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Compiler (ClosureCompilable(..), Closure(..))
import qualified Language.Vanillalog.Generic.Logger as L
import           Language.Vanillalog.Generic.Parser.SrcLoc
import           Language.Vanillalog.Generic.Pretty ( Pretty(..)
                                                    , HasPrecedence(..)
                                                    )

type Program = AG.Program Declaration HOp (BOp 'Temporal)

type Statement = AG.Statement Declaration HOp (BOp 'Temporal)

type Sentence = AG.Sentence HOp (BOp 'Temporal)

type Query = AG.Query HOp (BOp 'Temporal)

type Clause = AG.Clause HOp (BOp 'Temporal)

type Fact = AG.Fact HOp

type Subgoal = AG.Subgoal

data Declaration = Declaration
  { _span :: SrcSpan
  , _atomType :: AG.AtomicFormula AG.TermType
  , _timePredSyms :: Maybe [ AG.PredicateSymbol ]
  }

data Temporal = Temporal | ATemporal

data BOp (switch :: Temporal) (k :: AG.OpKind) where
  Negation      ::                                  BOp a    'AG.Unary
  Conjunction   ::                                  BOp a    'AG.Binary
  Disjunction   ::                                  BOp a    'AG.Binary

  Dogru         ::                                  BOp a    'AG.Nullary

  AX            :: AG.PredicateSymbol ->            BOp 'Temporal 'AG.Unary
  EX            :: AG.PredicateSymbol ->            BOp 'Temporal 'AG.Unary
  AG            :: AG.PredicateSymbol ->            BOp 'Temporal 'AG.Unary
  EG            :: AG.PredicateSymbol ->            BOp 'Temporal 'AG.Unary
  AF            :: AG.PredicateSymbol ->            BOp 'Temporal 'AG.Unary
  EF            :: AG.PredicateSymbol ->            BOp 'Temporal 'AG.Unary
  AU            :: AG.PredicateSymbol ->            BOp 'Temporal 'AG.Binary
  EU            :: AG.PredicateSymbol ->            BOp 'Temporal 'AG.Binary
  Bind          :: AG.PredicateSymbol -> AG.Var  -> BOp 'Temporal 'AG.Unary
  BodyJump      :: AG.PredicateSymbol -> AG.Term -> BOp 'Temporal 'AG.Unary

data HOp (k :: AG.OpKind) where
  HeadJump      :: AG.PredicateSymbol -> AG.Term -> HOp 'AG.Unary

deriving instance Ord (HOp opKind)
deriving instance Ord (BOp a opKind)

deriving instance Eq (HOp opKind)
deriving instance Eq (BOp a opKind)

pattern SAtom span atom      = AG.SAtom span atom
pattern SNeg  span sub       = AG.SUnOp span Negation sub
pattern SConj span sub1 sub2 = AG.SBinOp span Conjunction sub1 sub2
pattern SDisj span sub1 sub2 = AG.SBinOp span Disjunction sub1 sub2

pattern SDogru span = AG.SNullOp span Dogru

pattern SAX span timePredSym child = AG.SUnOp span (AX timePredSym) child
pattern SEX span timePredSym child = AG.SUnOp span (EX timePredSym) child
pattern SAG span timePredSym child = AG.SUnOp span (AG timePredSym) child
pattern SEG span timePredSym child = AG.SUnOp span (EG timePredSym) child
pattern SAF span timePredSym child = AG.SUnOp span (AF timePredSym) child
pattern SEF span timePredSym child = AG.SUnOp span (EF timePredSym) child
pattern SAU span timePredSym child1 child2 = AG.SBinOp span (AU timePredSym) child1 child2
pattern SEU span timePredSym child1 child2 = AG.SBinOp span (EU timePredSym) child1 child2

pattern SBind     span timePredSym var child  = AG.SUnOp span (Bind     timePredSym var) child
pattern SHeadJump span child timePredSym time = AG.SUnOp span (HeadJump timePredSym time) child
pattern SBodyJump span child timePredSym time = AG.SUnOp span (BodyJump timePredSym time) child

pattern SAtomF span atom          = AG.SAtomF span atom
pattern SNegF  span child         = AG.SUnOpF span Negation child
pattern SConjF span child1 child2 = AG.SBinOpF span Conjunction child1 child2
pattern SDisjF span child1 child2 = AG.SBinOpF span Disjunction child1 child2

pattern SDogruF span = AG.SNullOpF span Dogru

pattern SAXF span timePredSym child = AG.SUnOpF span (AX timePredSym) child
pattern SEXF span timePredSym child = AG.SUnOpF span (EX timePredSym) child
pattern SAGF span timePredSym child = AG.SUnOpF span (AG timePredSym) child
pattern SEGF span timePredSym child = AG.SUnOpF span (EG timePredSym) child
pattern SAFF span timePredSym child = AG.SUnOpF span (AF timePredSym) child
pattern SEFF span timePredSym child = AG.SUnOpF span (EF timePredSym) child
pattern SAUF span timePredSym child1 child2 = AG.SBinOpF span (AU timePredSym) child1 child2
pattern SEUF span timePredSym child1 child2 = AG.SBinOpF span (EU timePredSym) child1 child2

pattern SBindF     span timePredSym var child  = AG.SUnOpF span (Bind     timePredSym var) child
pattern SHeadJumpF span child timePredSym time = AG.SUnOpF span (HeadJump timePredSym time) child
pattern SBodyJumpF span child timePredSym time = AG.SUnOpF span (BodyJump timePredSym time) child

-------------------------------------------------------------------------------
-- Utility functions
-------------------------------------------------------------------------------

class AG.HasVariables a => HasFreeVariables a where
  freeVars :: a -> [ AG.Var ]

instance HasFreeVariables Sentence where
  freeVars AG.SFact{..}   = freeVars _fact
  freeVars AG.SClause{..} = freeVars _clause
  freeVars AG.SQuery{..}  = freeVars _query

instance HasFreeVariables Clause where
  freeVars AG.Clause{..} = freeVars _head ++ freeVars _body

instance HasFreeVariables Query where
  freeVars AG.Query{..} = freeVars _body

instance HasFreeVariables Fact where
  freeVars AG.Fact{..} = freeVars _head

instance HasFreeVariables (AG.AtomicFormula t)
    => HasFreeVariables (AG.Subgoal HOp t) where
  freeVars = cata varAlg
    where
    varAlg :: Base (AG.Subgoal HOp t) [ AG.Var ] -> [ AG.Var ]
    varAlg (SHeadJumpF _ vars _ term)   =
      case term of { AG.TVar v -> v : vars; _ -> vars }
    varAlg (SAtomF _ atom)              = freeVars atom
    varAlg (AG.SNullOpF _ _)            = []
    varAlg (AG.SUnOpF _ _ vars)         = vars
    varAlg (AG.SBinOpF _ _ vars1 vars2) = vars1 ++ vars2

instance HasFreeVariables (AG.AtomicFormula t)
    => HasFreeVariables (AG.Subgoal (BOp a) t) where
  freeVars = cata varAlg
    where
    varAlg :: Base (AG.Subgoal (BOp a) t) [ AG.Var ] -> [ AG.Var ]
    varAlg (SBodyJumpF _ vars _ term)   =
      case term of { AG.TVar v -> v : vars; _ -> vars }
    varAlg (SBindF _ _ var vars)        = var : vars
    varAlg (SAtomF _ atom)              = freeVars atom
    varAlg (AG.SNullOpF _ _)            = []
    varAlg (AG.SUnOpF _ _ vars)         = vars
    varAlg (AG.SBinOpF _ _ vars1 vars2) = vars1 ++ vars2

instance HasFreeVariables (AG.AtomicFormula AG.Term) where
  freeVars = AG.vars

instance HasFreeVariables (AG.AtomicFormula AG.Var) where
  freeVars = AG.vars

instance HasFreeVariables (AG.AtomicFormula AG.Sym) where
  freeVars = AG.vars

-------------------------------------------------------------------------------
-- Pretty printing related instances
-------------------------------------------------------------------------------

instance HasPrecedence (BOp a) where
  precedence AG.NoOp                 = 0
  precedence (AG.SomeOp Dogru)       = 0
  precedence (AG.SomeOp Negation)    = 1
  precedence (AG.SomeOp EX{})        = 1
  precedence (AG.SomeOp EF{})        = 1
  precedence (AG.SomeOp EG{})        = 1
  precedence (AG.SomeOp AX{})        = 1
  precedence (AG.SomeOp AF{})        = 1
  precedence (AG.SomeOp AG{})        = 1
  precedence (AG.SomeOp Conjunction) = 2
  precedence (AG.SomeOp Disjunction) = 3
  precedence (AG.SomeOp EU{})        = 4
  precedence (AG.SomeOp AU{})        = 4
  precedence (AG.SomeOp Bind{})      = 5
  precedence (AG.SomeOp BodyJump{})  = 6

instance HasPrecedence HOp where
  precedence AG.NoOp                = 0
  precedence (AG.SomeOp HeadJump{}) = 1

instance Pretty (BOp a opKind) where
  pretty Dogru                       = "TRUE"
  pretty Negation                    = "!"
  pretty Conjunction                 = ", "
  pretty Disjunction                 = "; "
  pretty (EX timePredSym)            = "EX" <+> pretty timePredSym <> " "
  pretty (EF timePredSym)            = "EF" <+> pretty timePredSym <> " "
  pretty (EG timePredSym)            = "EG" <+> pretty timePredSym <> " "
  pretty (EU timePredSym)            = " EU" <+> pretty timePredSym <> " "
  pretty (AX timePredSym)            = "AX" <+> pretty timePredSym <> " "
  pretty (AF timePredSym)            = "AF" <+> pretty timePredSym <> " "
  pretty (AG timePredSym)            = "AG" <+> pretty timePredSym <> " "
  pretty (AU timePredSym)            = " AU" <+> pretty timePredSym <> " "
  pretty (Bind timePredSym var)      = pretty timePredSym <+> pretty var  <+> "| "
  pretty (BodyJump timePredSym time) = pretty timePredSym <+> pretty time <+> "@ "

instance Pretty (HOp opKind) where
  pretty (HeadJump timePredSym time) = pretty timePredSym <+> pretty time <+> "@ "

instance Pretty Declaration where
  pretty (Declaration _ atom mTimes) =
    "decl" <+> pretty atom <+> "@" <+?> maybe empty (hcat . punctuate "," . prettyC) mTimes <> "."
