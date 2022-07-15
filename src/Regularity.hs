{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Regularity where

import Control.Monad
import Data.Data
import GHC.Plugins
import Unfold

-- | Annotates regular definitions.
data Regular
  = Regular
  deriving stock (Data)

plugin :: Plugin
plugin =
  defaultPlugin
    { installCoreToDos = \_ _ -> pure [CoreDoPluginPass "Plugin" go],
      pluginRecompile = purePlugin
    }
  where
    go :: ModGuts -> CoreM ModGuts
    go mguts = do
      forM_ (mg_anns mguts) $ \case
        Annotation (NamedTarget name) (fromSerialized deserializeWithData -> Just Regular) ->
          forM_ (flattenBinds $ mg_binds mguts) $ \(x, defn) -> do
            when (getName x == name) $ do
              let (xs, body) = collectBinders defn
                  goal = Goal (filter isId xs) body

              let ?scope = mkInScopeSet (mkVarSet (bindersOfBinds (mg_binds mguts)))
                  ?defns = mkVarEnv (flattenBinds (mg_binds mguts))
              res <- unfold goal
              pprTraceM "Definition:" (ppr x)
              pprTraceM "Rank:" (ppr $ length res)
        otherAnn -> pure ()
      pure mguts