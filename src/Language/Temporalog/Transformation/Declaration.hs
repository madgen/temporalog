{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.Transformation.Declaration where

import Protolude

import qualified Language.Vanillalog.Generic.Logger as Log
import qualified Language.Vanillalog.Generic.AST as AG

import Language.Temporalog.AST

removeDecls :: Program -> AG.Program Void Op
removeDecls AG.Program{..} = AG.Program{_statements = newStatements,..}
  where
  newStatements :: [ AG.Statement Void Op ]
  newStatements = map (\AG.StSentence{..} -> AG.StSentence{..})
                . filter (\case {AG.StSentence{} -> True; _ -> False})
                $ _statements
