module Language.Temporalog.Transformation.Temporal.JoinInjection
  ( injectJoins
  ) where

import Protolude

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

injectJoins :: [ JoinDeclaration ] -> MD.Metadata -> Program e -> Program e
injectJoins = _

data Join

processJoinDecls :: [ JoinDeclaration ] -> [ Join ]
processJoinDecls = _
