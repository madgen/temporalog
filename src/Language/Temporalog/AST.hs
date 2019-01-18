{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

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
  , pattern SEX, pattern SEF, pattern SEG, pattern SEU
  , pattern SAX, pattern SAF, pattern SAG, pattern SAU
  , pattern SHeadAt, pattern SBodyAt
  , pattern SEXF, pattern SEFF, pattern SEGF, pattern SEUF
  , pattern SAXF, pattern SAFF, pattern SAGF, pattern SAUF
  , pattern SHeadAtF, pattern SBodyAtF
  , HOp(..), BOp(..), AG.OpKind(..), AG.SomeOp(..)
  , AG.AtomicFormula(..)
  , AG.PredicateSymbol(..)
  , AG.Term(..)
  , AG.TermType(..)
  , AG.termType
  , AG.Var(..)
  , AG.Sym(..)
  , AG.vars
  , AG.operation
  ) where

import Protolude hiding ((<>), empty)

import qualified Data.List.NonEmpty as NE

import qualified Language.Exalog.Core as E

import Text.PrettyPrint ((<+>), (<>), int, empty)

import           Language.Exalog.Pretty.Helper ((<+?>))

import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Compiler (ClosureCompilable(..), Closure(..))
import qualified Language.Vanillalog.Generic.Logger as L
import           Language.Vanillalog.Generic.Parser.SrcLoc
import           Language.Vanillalog.Generic.Pretty ( Pretty(..)
                                                    , HasPrecedence(..)
                                                    )

type Program = AG.Program Declaration HOp BOp

type Statement = AG.Statement Declaration HOp BOp

type Sentence = AG.Sentence HOp BOp

type Query = AG.Query HOp BOp

type Clause = AG.Clause HOp BOp

type Fact = AG.Fact HOp

type Subgoal = AG.Subgoal

data Declaration = Declaration
  { _span :: SrcSpan
  , _atomType :: AG.AtomicFormula AG.TermType
  , _timePredSym :: Maybe AG.PredicateSymbol
  }

data BOp (k :: AG.OpKind) where
  Negation    ::            BOp 'AG.Unary
  Conjunction ::            BOp 'AG.Binary
  Disjunction ::            BOp 'AG.Binary

  Dogru       ::            BOp 'AG.Nullary

  AX          ::            BOp 'AG.Unary
  EX          ::            BOp 'AG.Unary
  AG          ::            BOp 'AG.Unary
  EG          ::            BOp 'AG.Unary
  AF          ::            BOp 'AG.Unary
  EF          ::            BOp 'AG.Unary
  AU          ::            BOp 'AG.Binary
  EU          ::            BOp 'AG.Binary
  BodyAt      :: AG.Term -> BOp 'AG.Unary

data HOp (k :: AG.OpKind) where
  HeadAt      :: AG.Term -> HOp 'AG.Unary

deriving instance Ord (HOp opKind)
deriving instance Ord (BOp opKind)

deriving instance Eq (HOp opKind)
deriving instance Eq (BOp opKind)

pattern SAtom span atom      = AG.SAtom span atom
pattern SNeg  span sub       = AG.SUnOp span Negation sub
pattern SConj span sub1 sub2 = AG.SBinOp span Conjunction sub1 sub2
pattern SDisj span sub1 sub2 = AG.SBinOp span Disjunction sub1 sub2

pattern SAX span child = AG.SUnOp span AX child
pattern SEX span child = AG.SUnOp span EX child
pattern SAG span child = AG.SUnOp span AG child
pattern SEG span child = AG.SUnOp span EG child
pattern SAF span child = AG.SUnOp span AF child
pattern SEF span child = AG.SUnOp span EF child
pattern SAU span child1 child2 = AG.SBinOp span AU child1 child2
pattern SEU span child1 child2 = AG.SBinOp span EU child1 child2

pattern SHeadAt span child time = AG.SUnOp span (HeadAt time) child
pattern SBodyAt span child time = AG.SUnOp span (BodyAt time) child

pattern SAtomF span atom          = AG.SAtomF span atom
pattern SNegF  span child         = AG.SUnOpF span Negation child
pattern SConjF span child1 child2 = AG.SBinOpF span Conjunction child1 child2
pattern SDisjF span child1 child2 = AG.SBinOpF span Disjunction child1 child2

pattern SAXF span child = AG.SUnOpF span AX child
pattern SEXF span child = AG.SUnOpF span EX child
pattern SAGF span child = AG.SUnOpF span AG child
pattern SEGF span child = AG.SUnOpF span EG child
pattern SAFF span child = AG.SUnOpF span AF child
pattern SEFF span child = AG.SUnOpF span EF child
pattern SAUF span child1 child2 = AG.SBinOpF span AU child1 child2
pattern SEUF span child1 child2 = AG.SBinOpF span EU child1 child2

pattern SHeadAtF span child time = AG.SUnOpF span (HeadAt time) child
pattern SBodyAtF span child time = AG.SUnOpF span (BodyAt time) child

-------------------------------------------------------------------------------
-- Pretty printing related instances
-------------------------------------------------------------------------------

instance HasPrecedence BOp where
  precedence AG.NoOp                 = 0
  precedence (AG.SomeOp Negation)    = 1
  precedence (AG.SomeOp EX)          = 1
  precedence (AG.SomeOp EF)          = 1
  precedence (AG.SomeOp EG)          = 1
  precedence (AG.SomeOp AX)          = 1
  precedence (AG.SomeOp AF)          = 1
  precedence (AG.SomeOp AG)          = 1
  precedence (AG.SomeOp Conjunction) = 2
  precedence (AG.SomeOp Disjunction) = 3
  precedence (AG.SomeOp EU)          = 4
  precedence (AG.SomeOp AU)          = 4
  precedence (AG.SomeOp BodyAt{})    = 5

instance HasPrecedence HOp where
  precedence AG.NoOp              = 0
  precedence (AG.SomeOp HeadAt{}) = 1

instance Pretty (BOp opKind) where
  pretty Dogru         = "TRUE"
  pretty Negation      = "!"
  pretty Conjunction   = ", "
  pretty Disjunction   = "; "
  pretty EX            = "EX "
  pretty EF            = "EF "
  pretty EG            = "EG "
  pretty EU            = " EU "
  pretty AX            = "AX "
  pretty AF            = "AF "
  pretty AG            = "AG "
  pretty AU            = " AU "
  pretty (BodyAt time) = pretty time <+> "@ "

instance Pretty (HOp opKind) where
  pretty (HeadAt time) = pretty time <+> "@ "

instance Pretty Declaration where
  pretty (Declaration _ atom mTime) =
    "decl" <+> pretty atom <+> "@" <+?> maybe empty pretty mTime <> "."
