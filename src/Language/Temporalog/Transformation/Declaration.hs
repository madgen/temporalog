{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.Transformation.Declaration where

import Protolude

import qualified Language.Vanillalog.Generic.AST as AG

import Language.Temporalog.AST

removeDecls :: Program -> AG.Program Void HOp (BOp 'Temporal)
removeDecls AG.Program{..} = AG.Program{_statements = newStatements,..}
  where
  newStatements :: [ AG.Statement Void HOp (BOp 'Temporal) ]
  newStatements = map (\AG.StSentence{..} -> AG.StSentence{..})
                . filter (\case {AG.StSentence{} -> True; _ -> False})
                $ _statements
