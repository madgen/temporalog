{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Transformation.Temporal.Vanilla (toVanilla) where

import Protolude

import           Language.Temporalog.AST

import qualified Language.Vanillalog.AST as A
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log

toVanilla :: AG.Program Void (Const Void) (BOp 'ATemporal)
          -> Log.LoggerM A.Program
toVanilla _ = _
