{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Temporalog.AST
  ( Program(..)
  , Statement(..)
  , Declaration(..)
  , Sentence(..)
  , Query(..)
  , Clause(..)
  , AG.Fact(..)
  , Subgoal
  , pattern SAtom, pattern SNeg, pattern SConj, pattern SDisj
  , pattern SAtomF, pattern SNegF, pattern SConjF, pattern SDisjF
  , pattern SEX, pattern SEF, pattern SEG, pattern SEU
  , pattern SAX, pattern SAF, pattern SAG, pattern SAU
  , pattern SEXF, pattern SEFF, pattern SEGF, pattern SEUF
  , pattern SAXF, pattern SAFF, pattern SAGF, pattern SAUF
  , Op(..), AG.OpKind(..), AG.SomeOp(..)
  , AG.AtomicFormula(..)
  , AG.Term(..)
  , AG.Var(..)
  , AG.Sym(..)
  , AG.vars
  , AG.operation
  ) where

import Protolude hiding ((<>), empty)

import qualified Data.List.NonEmpty as NE

import qualified Language.Exalog.Core as E

import Text.PrettyPrint ((<+>), (<>), int, empty)

import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Compiler (ClosureCompilable(..), Closure(..))
import qualified Language.Vanillalog.Generic.Logger as L
import           Language.Vanillalog.Generic.Parser.SrcLoc
import           Language.Vanillalog.Generic.Pretty ( Pretty(..)
                                                    , HasPrecedence(..)
                                                    )

type Program = AG.Program Declaration Op

type Statement = AG.Statement Declaration Op

type Sentence = AG.Sentence Op

type Query = AG.Query Op

type Clause = AG.Clause Op

type Subgoal = AG.Subgoal Op

data Declaration = Declaration
  { _span :: SrcSpan
  , _predSym :: Text
  , _arity :: Int
  , _timePredSym :: Maybe Text
  }

data Op (k :: AG.OpKind) where
  Negation    :: Op 'AG.Unary
  Conjunction :: Op 'AG.Binary
  Disjunction :: Op 'AG.Binary

  Dogru       :: Op 'AG.Nullary

  AX          :: Op 'AG.Unary
  EX          :: Op 'AG.Unary
  AG          :: Op 'AG.Unary
  EG          :: Op 'AG.Unary
  AF          :: Op 'AG.Unary
  EF          :: Op 'AG.Unary
  AU          :: Op 'AG.Binary
  EU          :: Op 'AG.Binary

deriving instance Eq (Op opKind)

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

-------------------------------------------------------------------------------
-- Pretty printing related instances
-------------------------------------------------------------------------------

instance HasPrecedence Op where
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

instance Pretty (Op opKind) where
  pretty Dogru       = "TRUE"
  pretty Negation    = "!"
  pretty Conjunction = ", "
  pretty Disjunction = "; "
  pretty EX          = "EX "
  pretty EF          = "EF "
  pretty EG          = "EG "
  pretty EU          = " EU "
  pretty AX          = "AX "
  pretty AF          = "AF "
  pretty AG          = "AG "
  pretty AU          = " AU "

instance Pretty Declaration where
  pretty (Declaration _ pred arity mTime) =
    "decl" <+> pretty pred <+> int arity <+> maybe empty pretty mTime <> "."
