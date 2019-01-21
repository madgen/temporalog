{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Transformation.Temporal.CTL (eliminateTemporal) where

import Protolude

import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import qualified Language.Vanillalog.AST as A

import Language.Temporalog.AST

eliminateTemporal :: AG.Program Void HOp (BOp AtOn) -> Log.LoggerM A.Program
eliminateTemporal = _
