module Language.Temporalog.Transformation.Declaration where

import Protolude

import qualified Language.Vanillalog.Generic.Logger as Log
import qualified Language.Vanillalog.Generic.AST as GA

import Language.Temporalog.AST

removeDecls :: Program -> Log.LoggerM (GA.Program Void Op)
removeDecls = _
