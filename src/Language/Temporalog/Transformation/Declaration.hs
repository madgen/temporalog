{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Temporalog.Transformation.Declaration where

import Protolude

import qualified Language.Vanillalog.Generic.AST as AG

import Language.Temporalog.AST

removeDecls :: forall eleb
             . Program eleb -> AG.Program Void (HOp eleb) (BOp eleb 'Temporal)
removeDecls AG.Program{..} = AG.Program{_statements = newStatements,..}
  where
  newStatements :: [ AG.Statement Void (HOp eleb) (BOp eleb 'Temporal) ]
  newStatements = map (\AG.StSentence{..} -> AG.StSentence{..})
                . filter (\case {AG.StSentence{} -> True; _ -> False})
                $ _statements
