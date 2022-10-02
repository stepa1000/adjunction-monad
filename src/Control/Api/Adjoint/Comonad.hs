{-# Language TypeOperators, TypeFamilies, GADTs
 , TypeApplications, ScopedTypeVariables
 , FlexibleContexts #-}

module Control.Api.Adjoint.Comonad where

import GHC.Generics

import Data.Functor.Adjunction
import Data.Typeable
import Data.Foldable

import Control.Comonad.Trans.Adjoint
import Control.Comonad

import Control.Monad.Free
import Control.Comonad.Cofree

import Control.Comonad.Trans.Env
import Control.Monad.Reader

import Control.Monad.Writer.Lazy
import Control.Comonad.Trans.Traced

import Control.Api.Adjoint.Monad
import Control.Comonad.Adjoint

data AdjointApiW api w a where
  CompAdjApiW :: (AdjVar api1, AdjVar api2, Typeable api1, Typeable api2
	, Typeable a, Typeable b
	, Adjunction (FAdjVar api1) (GAdjVar api1)
	, Adjunction (FAdjVar api2) (GAdjVar api2)
	) => AdjointApiW api1 w a -> AdjointApiW api2 w b -> AdjointApiW (api1 :..: api2) w (a,b)
  CombAdjApiW :: (AdjVar api1, AdjVar api2, Typeable api1, Typeable api2
	, Typeable a, Typeable b
	, Adjunction (FAdjVar api1) (GAdjVar api1)
	, Adjunction (FAdjVar api2) (GAdjVar api2)
	) => AdjointApiW api1 w a -> AdjointApiW api2 w b -> AdjointApiW (api1 :+*: api2) w (Either a b)
  AdjApiW :: AdjointT (FAdjVar api) (GAdjVar api) w a -> AdjointApiW api w a

compilAdjointApiW :: (AdjVar api, Typeable api, Typeable a
	, Adjunction (FAdjVar api) (GAdjVar api)
	, ComonadApply w
	)
	=> Proxy (api,a) -> AdjointApiW api w a ->[AdjointT (FAdjVar api) (GAdjVar api) w a]
compilAdjointApiW _ (AdjApiW a) = return a
compilAdjointApiW (p :: Proxy (api,a)) (CompAdjApiW (a1 :: AdjointApiW api1 w x) (a2 :: AdjointApiW api2 w y)) = do
	toList $ eqT @(api1 :..: api2) @api
	toList $ eqT @a @(x,y)
	v1 <- compilAdjointApiW (Proxy :: Proxy (api1,x)) a1
	v2 <- compilAdjointApiW (Proxy :: Proxy (api2,y)) a2
	return $ compAdjoint v1 v2
compilAdjointApiW (p :: Proxy (api,a)) (CombAdjApiW (a1 :: AdjointApiW api1 w x) (a2 :: AdjointApiW api2 w y)) = do
	toList $ eqT @(api1 :+*: api2) @api
	toList $ eqT @a @(Either x y)
	v1 <- compilAdjointApiW (Proxy :: Proxy (api1,x)) a1
	v2 <- compilAdjointApiW (Proxy :: Proxy (api2,y)) a2
	combAdjoint v1 v2


