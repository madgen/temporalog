{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Transformation.Temporal.Elaborator
  ( elaborate
  ) where

import Protolude

import Language.Exalog.Logger

import Language.Temporalog.AST

elaborate :: Program 'Implicit -> Logger (Program 'Explicit)
elaborate = _
