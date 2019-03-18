{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Transformation.Temporal.CTL (eliminateTemporal) where

import Protolude

import Control.Arrow ((>>>))

import Data.Functor.Foldable (Base, cata, embed)

import qualified Language.Vanillalog.AST as A
import           Language.Vanillalog.Generic.Transformation.Util (Algebra, transformBody)
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Parser.SrcLoc (span)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

eliminateTemporal :: MD.Metadata
                  -> AG.Program Void HOp (BOp 'Temporal)
                  -> Log.LoggerM (AG.Program Void (Const Void) (BOp 'ATemporal))
eliminateTemporal = round3

round3 :: MD.Metadata
       -> AG.Program Void HOp (BOp 'Temporal)
       -> Log.LoggerM (AG.Program Void (Const Void) (BOp 'ATemporal))
round3 = _
