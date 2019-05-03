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
injectJoins meta AG.Program{..} = _
