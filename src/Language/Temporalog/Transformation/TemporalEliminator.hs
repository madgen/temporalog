module Language.Temporalog.Transformation.TemporalEliminator
  ( eliminateTemporal
  ) where

import qualified Language.Vanillalog.Generic.AST as VAG
import qualified Language.Vanillalog.Generic.Logger as Log
import qualified Language.Vanillalog.AST as VA

import Language.Temporalog.AST

eliminateTemporal :: VAG.Program Op -> Log.LoggerM (VAG.Program VA.Op)
eliminateTemporal = _
