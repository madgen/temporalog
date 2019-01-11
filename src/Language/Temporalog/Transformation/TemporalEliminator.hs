module Language.Temporalog.Transformation.TemporalEliminator
  ( eliminateTemporal
  ) where

import Protolude

import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import qualified Language.Vanillalog.AST as A

import Language.Temporalog.AST

eliminateTemporal :: AG.Program Void HOp BOp -> Log.LoggerM A.Program
eliminateTemporal = _
