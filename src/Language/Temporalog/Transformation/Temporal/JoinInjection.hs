module Language.Temporalog.Transformation.Temporal.JoinInjection
  ( injectJoins
  ) where

import Protolude

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

injectJoins :: MD.Metadata -> Program e -> Program e
injectJoins = _
