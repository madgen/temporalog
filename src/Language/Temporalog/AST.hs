{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Temporalog.AST
  ( Program
  , Statement
  , Declaration(..)
  , PredicateDeclaration(..), JoinDeclaration(..)
  , Sentence
  , Query
  , Clause
  , Fact
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
  , TimeSym(..)
  , HOp(..), BOp(..), ElaborationStatus(..), Temporal(..) , AG.OpKind(..)
  , timePred
  , AG.SomeOp(..)
  , AG.AtomicFormula(..)
  , PredicateSymbol(..)
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

import Text.PrettyPrint ((<+>), (<>), empty, punctuate, hcat)

import           Language.Exalog.Pretty.Helper ((<+?>), prettyC)

import           Language.Exalog.Core (PredicateSymbol(..))
import           Language.Exalog.SrcLoc

import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Pretty ( Pretty(..)
                                                    , HasPrecedence(..)
                                                    )

type Program eleb = AG.Program Declaration (HOp eleb) (BOp eleb 'Temporal)

type Statement eleb = AG.Statement Declaration (HOp eleb) (BOp eleb 'Temporal)

type Sentence eleb = AG.Sentence (HOp eleb) (BOp eleb 'Temporal)

type Query eleb = AG.Query (HOp eleb) (BOp eleb 'Temporal)

type Clause eleb = AG.Clause (HOp eleb) (BOp eleb 'Temporal)

type Fact eleb = AG.Fact (HOp eleb)

type Subgoal = AG.Subgoal

data Declaration =
    DeclPred {_predDecl :: PredicateDeclaration}
  | DeclJoin {_joinDecl :: JoinDeclaration}

data PredicateDeclaration = PredicateDeclaration
  { _span         :: SrcSpan
  , _atomType     :: AG.AtomicFormula AG.TermType
  , _timePredSyms :: Maybe [ PredicateSymbol ]
  }

data JoinDeclaration = JoinDeclaration
  { _span           :: SrcSpan
  , _joint          :: PredicateSymbol
  }

data ElaborationStatus = Explicit | Implicit

data TimeSym :: ElaborationStatus -> Type where
  Imp ::                    TimeSym 'Implicit
  Exp :: PredicateSymbol -> TimeSym eleb

deriving instance Eq (TimeSym eleb)
deriving instance Ord (TimeSym eleb)

data Temporal = Temporal | ATemporal

data BOp :: ElaborationStatus -> Temporal -> AG.OpKind -> Type where
  Negation      ::                            BOp eleb temp      'AG.Unary
  Conjunction   ::                            BOp eleb temp      'AG.Binary
  Disjunction   ::                            BOp eleb temp      'AG.Binary

  Dogru         ::                            BOp eleb temp      'AG.Nullary

  AX            :: TimeSym eleb ->            BOp eleb 'Temporal 'AG.Unary
  EX            :: TimeSym eleb ->            BOp eleb 'Temporal 'AG.Unary
  AG            :: TimeSym eleb ->            BOp eleb 'Temporal 'AG.Unary
  EG            :: TimeSym eleb ->            BOp eleb 'Temporal 'AG.Unary
  AF            :: TimeSym eleb ->            BOp eleb 'Temporal 'AG.Unary
  EF            :: TimeSym eleb ->            BOp eleb 'Temporal 'AG.Unary
  AU            :: TimeSym eleb ->            BOp eleb 'Temporal 'AG.Binary
  EU            :: TimeSym eleb ->            BOp eleb 'Temporal 'AG.Binary
  Bind          :: TimeSym eleb -> AG.Var  -> BOp eleb 'Temporal 'AG.Unary
  BodyJump      :: TimeSym eleb -> AG.Term -> BOp eleb 'Temporal 'AG.Unary

timePred :: BOp 'Explicit temp a -> Maybe PredicateSymbol
timePred op =
  case op of
    AX (Exp timePred)         -> Just timePred
    EX (Exp timePred)         -> Just timePred
    AG (Exp timePred)         -> Just timePred
    EG (Exp timePred)         -> Just timePred
    AF (Exp timePred)         -> Just timePred
    EF (Exp timePred)         -> Just timePred
    AU (Exp timePred)         -> Just timePred
    EU (Exp timePred)         -> Just timePred
    Bind (Exp timePred) _     -> Just timePred
    BodyJump (Exp timePred) _ -> Just timePred
    _                         -> Nothing

data HOp :: ElaborationStatus -> AG.OpKind -> Type where
  HeadJump      :: TimeSym eleb -> AG.Term -> HOp eleb 'AG.Unary

deriving instance Ord (HOp eleb opKind)
deriving instance Ord (BOp eleb temp opKind)

deriving instance Eq (HOp eleb opKind)
deriving instance Eq (BOp eleb temp opKind)

pattern SAtom span atom      = AG.SAtom span atom
pattern SNeg  span sub       = AG.SUnOp span Negation sub
pattern SConj span sub1 sub2 = AG.SBinOp span Conjunction sub1 sub2
pattern SDisj span sub1 sub2 = AG.SBinOp span Disjunction sub1 sub2

pattern SDogru span = AG.SNullOp span Dogru

pattern SAX span timeSym phi = AG.SUnOp span (AX timeSym) phi
pattern SEX span timeSym phi = AG.SUnOp span (EX timeSym) phi
pattern SAG span timeSym phi = AG.SUnOp span (AG timeSym) phi
pattern SEG span timeSym phi = AG.SUnOp span (EG timeSym) phi
pattern SAF span timeSym phi = AG.SUnOp span (AF timeSym) phi
pattern SEF span timeSym phi = AG.SUnOp span (EF timeSym) phi
pattern SAU span timeSym phi psi = AG.SBinOp span (AU timeSym) phi psi
pattern SEU span timeSym phi psi = AG.SBinOp span (EU timeSym) phi psi

pattern SBind     span timeSym var phi  = AG.SUnOp span (Bind     timeSym var)  phi
pattern SHeadJump span phi timeSym time = AG.SUnOp span (HeadJump timeSym time) phi
pattern SBodyJump span phi timeSym time = AG.SUnOp span (BodyJump timeSym time) phi

pattern SAtomF span atom          = AG.SAtomF span atom
pattern SNegF  span child         = AG.SUnOpF span Negation child
pattern SConjF span child1 child2 = AG.SBinOpF span Conjunction child1 child2
pattern SDisjF span child1 child2 = AG.SBinOpF span Disjunction child1 child2

pattern SDogruF span = AG.SNullOpF span Dogru

pattern SAXF span timeSym child = AG.SUnOpF span (AX timeSym) child
pattern SEXF span timeSym child = AG.SUnOpF span (EX timeSym) child
pattern SAGF span timeSym child = AG.SUnOpF span (AG timeSym) child
pattern SEGF span timeSym child = AG.SUnOpF span (EG timeSym) child
pattern SAFF span timeSym child = AG.SUnOpF span (AF timeSym) child
pattern SEFF span timeSym child = AG.SUnOpF span (EF timeSym) child
pattern SAUF span timeSym child1 child2 = AG.SBinOpF span (AU timeSym) child1 child2
pattern SEUF span timeSym child1 child2 = AG.SBinOpF span (EU timeSym) child1 child2

pattern SBindF     span timeSym var child  = AG.SUnOpF span (Bind     timeSym var) child
pattern SHeadJumpF span child timeSym time = AG.SUnOpF span (HeadJump timeSym time) child
pattern SBodyJumpF span child timeSym time = AG.SUnOpF span (BodyJump timeSym time) child

-------------------------------------------------------------------------------
-- Utility functions
-------------------------------------------------------------------------------

class AG.HasVariables a => HasFreeVariables a where
  freeVars :: a -> [ AG.Var ]

instance HasFreeVariables (Sentence eleb) where
  freeVars AG.SFact{..}   = freeVars _fact
  freeVars AG.SClause{..} = freeVars _clause
  freeVars AG.SQuery{..}  = freeVars _query

instance HasFreeVariables (Clause eleb) where
  freeVars AG.Clause{..} = freeVars _head ++ freeVars _body

instance HasFreeVariables (Query eleb) where
  freeVars AG.Query{..} = freeVars _body

instance HasFreeVariables (Fact eleb) where
  freeVars AG.Fact{..} = freeVars _head

instance HasFreeVariables (AG.AtomicFormula t)
    => HasFreeVariables (AG.Subgoal (HOp eleb) t) where
  freeVars = cata varAlg
    where
    varAlg :: Base (AG.Subgoal (HOp eleb) t) [ AG.Var ] -> [ AG.Var ]
    varAlg (SHeadJumpF _ vars _ term)   =
      case term of { AG.TVar v -> v : vars; _ -> vars }
    varAlg (AG.SAtomF _ atom)              = freeVars atom
    varAlg (AG.SNullOpF _ _)            = []
    varAlg (AG.SUnOpF _ _ vars)         = vars
    varAlg (AG.SBinOpF _ _ vars1 vars2) = vars1 ++ vars2

instance HasFreeVariables (AG.AtomicFormula t)
    => HasFreeVariables (AG.Subgoal (BOp eleb temp) t) where
  freeVars = cata varAlg
    where
    varAlg :: Base (AG.Subgoal (BOp eleb temp) t) [ AG.Var ] -> [ AG.Var ]
    varAlg (SBodyJumpF _ vars _ term)   =
      case term of { AG.TVar v -> v : vars; _ -> vars }
    varAlg (SBindF _ _ var vars)        = filter (var /=) vars
    varAlg (AG.SAtomF _ atom)           = freeVars atom
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

instance Spannable Declaration where
  span DeclPred{..} = span _predDecl
  span DeclJoin{..} = span _joinDecl

-------------------------------------------------------------------------------
-- Pretty printing related instances
-------------------------------------------------------------------------------

instance HasPrecedence (BOp eleb temp) where
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

instance HasPrecedence (HOp eleb) where
  precedence AG.NoOp                = 0
  precedence (AG.SomeOp HeadJump{}) = 1

instance Pretty (TimeSym eleb) where
  pretty (Exp predSym) = "<" <> pretty predSym <> ">"
  pretty Imp           = empty

instance Pretty (BOp eleb temp opKind) where
  pretty Dogru                   = "TRUE"
  pretty Negation                = "!"
  pretty Conjunction             = ", "
  pretty Disjunction             = "; "
  pretty (EX timeSym)            = "EX"  <+> pretty timeSym <> " "
  pretty (EF timeSym)            = "EF"  <+> pretty timeSym <> " "
  pretty (EG timeSym)            = "EG"  <+> pretty timeSym <> " "
  pretty (EU timeSym)            = " EU" <+> pretty timeSym <> " "
  pretty (AX timeSym)            = "AX"  <+> pretty timeSym <> " "
  pretty (AF timeSym)            = "AF"  <+> pretty timeSym <> " "
  pretty (AG timeSym)            = "AG"  <+> pretty timeSym <> " "
  pretty (AU timeSym)            = " AU" <+> pretty timeSym <> " "
  pretty (Bind timeSym var)      = pretty timeSym <+> pretty var  <+> "| "
  pretty (BodyJump timeSym time) = pretty timeSym <+> pretty time <+> "@ "

instance Pretty (HOp eleb opKind) where
  pretty (HeadJump timeSym time) = pretty timeSym <+> pretty time <+> "@ "

instance Pretty Declaration where
  pretty (DeclPred PredicateDeclaration{..}) =
    ".pred" <+> pretty _atomType
      <+> "@" <+?> maybe empty (hcat . prettyC) _timePredSyms <> "."
  pretty (DeclJoin JoinDeclaration{..}) =
    ".join" <+> pretty _joint <> "."
