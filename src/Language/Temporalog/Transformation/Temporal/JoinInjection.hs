{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.Transformation.Temporal.JoinInjection
  ( injectJoins
  ) where

import Protolude

import qualified Language.Vanillalog.Generic.AST as AG

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

injectJoins :: MD.Metadata
            -> AG.Program Void (HOp 'Explicit) (BOp 'Explicit 'Temporal)
            -> AG.Program Void (HOp 'Explicit) (BOp 'Explicit 'Temporal)
injectJoins meta AG.Program{..} =
  AG.Program{_statements = goSt <$> _statements, ..}
  where
  goSt (AG.StSentence sent)    = AG.StSentence $ goSent sent
  goSt (AG.StDeclaration decl) = AG.StDeclaration $ absurd decl

  goSent sent@AG.SFact{..}          = sent
  goSent (AG.SClause AG.Clause{..}) =
    AG.SClause AG.Clause{_body = goBody _body, ..}
  goSent (AG.SQuery AG.Query{..})   =
    AG.SQuery AG.Query{_body = goBody _body, ..}

  goBody = _
