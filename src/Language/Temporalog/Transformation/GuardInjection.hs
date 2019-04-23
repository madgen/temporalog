{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Temporalog.Transformation.GuardInjection
  ( injectGuards
  ) where

import Protolude hiding (head)

import qualified Data.Graph.Inductive as Gr
import           Data.List ((\\), nub, lookup)
import qualified Data.List.NonEmpty as NE
import           Data.Singletons (sing)
import           Data.Singletons.TypeLits (SNat)
import qualified Data.Vector.Sized as V

import           Language.Exalog.Adornment (adornProgram)
import           Language.Exalog.Core
import           Language.Exalog.Dependency
import           Language.Exalog.Logger
import           Language.Exalog.RangeRestriction (isRangeRestricted)
import           Language.Exalog.SrcLoc (span)
import           Language.Exalog.WellModing (isWellModed, checkWellModability)

import qualified Language.Temporalog.Metadata as MD
import           Language.Temporalog.Transformation.Fresh

type Injection = FreshT Logger

runFreshPredSymT :: Monad m => Program 'ABase -> FreshT m a -> m a
runFreshPredSymT Program{clauses = clauses} =
  runFreshT (Just "guard") ((\(PredicateSymbol text) -> text) <$> predSyms)
  where
  predSyms = join $ (`map` clauses) $ \Clause{..} ->
    predSym head : (predSym <$> NE.toList body)

  predSym Literal{predicate = Predicate{..}} = fxSym

freshPredSym :: Monad m => FreshT m PredicateSymbol
freshPredSym = PredicateSymbol <$> fresh

injectGuards :: MD.Metadata -> Program 'ABase -> Logger (Program 'ABase)
injectGuards metadata pr@Program{..} = runFreshPredSymT pr $ do
  injectedClausess <- traverse assessAndTransform temporalClusters

  pure $ Program
    { clauses = aTemporalClauses <> mconcat injectedClausess
    , ..}
  where
  temporalClusters :: [ Program 'ABase ]
  temporalClusters  = map isolateWithAuxillaries topLevelTemporalClauses

  aTemporalClauses :: [ Clause 'ABase ]
  aTemporalClauses =
    clauses \\ mconcat (map (\Program{clauses = clss} -> clss) temporalClusters)

  assessAndTransform :: Program 'ABase -> Injection [ Clause 'ABase ]
  assessAndTransform cluster@Program{clauses = clss}
    | isWellModed cluster && isRangeRestricted cluster = pure clss
    | otherwise = do
      lift $ checkWellModability (adornProgram cluster)
      injectGuard cluster

  injectGuard :: Program 'ABase -> Injection [ Clause 'ABase ]
  injectGuard cluster@Program{clauses = topClause : _} = do
    let (guardLits, bodyMinusGuard) = findGuard topClause

    case NE.nonEmpty guardLits of
      Just guardBody -> do
        guardSym <- freshPredSym

        let guardVars = nub . fmap TVar . join $ variables <$> guardLits

        V.withSizedList guardVars $ \(guardTerms :: V.Vector n Term) -> do

          let guardPred = Predicate
                { annotation = PredABase $ span topClause
                , fxSym      = guardSym
                , arity      = sing :: SNat n
                , nature     = Logical
                }

          let guardHead = Literal
                { annotation = LitABase $ span topClause
                , polarity   = Positive
                , predicate  = guardPred
                , terms      = guardTerms
                }

          let guardClause = Clause
                { annotation = ClABase $ span topClause
                , head       = guardHead
                , body       = guardBody
                }

          let newTopClause = Clause
                { annotation = ClABase $ span topClause
                , head       = head topClause
                , body       = NE.cons guardHead bodyMinusGuard
                }

          let topHead = predicateBox $ head topClause
          newAuxClss <- (`execStateT` []) $
            enterAuxillary
              guardHead cluster (unitSubst guardHead) topHead bodyMinusGuard

          pure $ newTopClause : guardClause : newAuxClss

      Nothing -> lift $ scold (Just $ span topClause) "Clause is ill-moded."
  injectGuard Program{clauses = []} = lift $
    scream Nothing "Empty cluster during guard injection."

  enterAuxillary :: Literal 'ABase      -- Guard literal
                 -> Program 'ABase      -- Cluster
                 -> VarSubstitution     -- Mapping needed for the guard literal
                 -> PredicateBox 'ABase -- Head of the clause being examined
                 -> Body 'ABase         -- Auxillary body being examined
                 -> StateT [ Clause 'ABase ] Injection ()
  enterAuxillary guardLit cluster subst headPBox examinedBody = do
    let targetLits = (`NE.filter` examinedBody) $ \lit -> runIdentity $ do
          let pBox = predicateBox lit
          pure $ pBox /= headPBox && pBoxIsAuxillary pBox
    (`traverse_` targetLits) $ \examinedLit -> do
      let targetClauses = search cluster (predicateBox examinedLit)
      (`traverse_` targetClauses) $ \targetClause@Clause{..} -> do
        let newSubst = subst `composeSubst` (examinedLit `deriveSubst` head)

        if isWellModed targetClause && isRangeRestricted targetClause
          then modify (targetClause :)
          else do
            let newGuardLit = newSubst `substLit` guardLit
            modify (targetClause {body = NE.cons newGuardLit body} :)

        enterAuxillary guardLit cluster newSubst (predicateBox head) body

  findGuard :: Clause 'ABase
            -> ( [ Literal 'ABase ] -- |Guard
               , Body 'ABase        -- |Rest of the body
               )
  findGuard Clause{body = body} =
    second NE.fromList . NE.span (not . pBoxIsAuxillary . predicateBox) $ body

  topLevelTemporalClauses :: [ Clause 'ABase ]
  topLevelTemporalClauses = filter isTopLevelTemporal clauses

  -- |A clause is top-level temporal clause if its
  -- + head is not an auxillary predicate
  -- + body contains an auxillary predicate
  isTopLevelTemporal :: Clause 'ABase -> Bool
  isTopLevelTemporal Clause{head = head, body = body} =
    not headIsAuxillary && bodyHasAuxillary
    where
    headIsAuxillary  = pBoxIsAuxillary . predicateBox $ head
    bodyHasAuxillary = or $ pBoxIsAuxillary . predicateBox <$> body

  pBoxIsAuxillary :: PredicateBox 'ABase -> Bool
  pBoxIsAuxillary (PredicateBox Predicate{fxSym = predSym}) =
    maybe False MD.isAuxillary (predSym `MD.lookup` metadata)

  depGr :: DependencyGr 'ABase
  depGr = dependencyGr . decorate $ pr

  bodyAuxillaries :: Body 'ABase -> [ PredicateBox 'ABase ]
  bodyAuxillaries phi = filter pBoxIsAuxillary $ NE.toList (predicateBox <$> phi)

  -- |Find auxillary predicates that appear in the body of the clause and
  -- find the auxillary predicates that appear in the defining clauses of
  -- those auxillary predicates and so on.
  findDirectAuxillaries :: Clause 'ABase -> [ PredicateBox 'ABase ]
  findDirectAuxillaries Clause{body = body} =
    Gr.xdfsWith chooseNode Gr.lab' initialNodes depGr
    where
    -- |All the auxillary nodes that appear in clause body
    initialNodes :: [ Gr.Node ]
    initialNodes = (`mapMaybe` Gr.labNodes depGr) $ \(node, pBox) ->
      if pBox `elem` bodyAuxillaries body then Just node else Nothing

    -- |Exploit the fact that auxillary predicates are never acyclic except
    -- perhaps reflexive.
    chooseNode :: Gr.Context (PredicateBox 'ABase) b -> [ Gr.Node ]
    chooseNode (nextNodes, _, pBox, _) = (`mapMaybe` nextNodes) $
      \(_, node) -> do
        pBox' <- Gr.lab depGr node
        if pBox /= pBox' && pBoxIsAuxillary pBox'
          then Just node
          else Nothing

  -- |Create a little program that has the target clause and all auxillary
  -- clauses that descend from it. The query predicate is set to the target
  -- clause head predicate.
  isolateWithAuxillaries :: Clause 'ABase -> Program 'ABase
  isolateWithAuxillaries cl = Program
    { clauses    = cl : mconcat (search pr <$> findDirectAuxillaries cl)
    , queryPreds = [ predicateBox . head $ cl ]
    , annotation = annotation
    }

--------------------------------------------------------------------------------
-- Variable substitutions
--------------------------------------------------------------------------------

type VarSubstitution = [ (Var, Var) ]

unitSubst :: Literal a -> VarSubstitution
unitSubst Literal{terms = ts} =
  mapMaybe (\case {TVar v -> Just (v,v); _ -> Nothing}) $ V.toList ts

-- |Derive a substitution by diffing two literals. Result when applied to
-- the first literal should make it look more like the second.
deriveSubst :: Literal a -> Literal a -> VarSubstitution
deriveSubst Literal{terms = ts} Literal{terms = ts'} =
  catMaybes $ zipWith pickSubst (V.toList ts) (V.toList ts')
  where
  pickSubst (TVar v) (TVar v') = Just (v,v')
  pickSubst _        _         = Nothing

substLit :: VarSubstitution -> Literal a -> Literal a
substLit subst Literal{..} = Literal
  { terms = substTerm subst <$> terms
  , ..}

-- |Replace variables using the substitution or make them wildcard if you
-- cannot find them.
substTerm :: VarSubstitution -> Term -> Term
substTerm subst (TVar v) = maybe TWild TVar (v `lookup` subst)
substTerm _     t        = t

composeSubst :: VarSubstitution -> VarSubstitution -> VarSubstitution
composeSubst s s' = (`mapMaybe` s) $ \(x,y) -> (x,) <$> (y `lookup` s')
