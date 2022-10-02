{-# Language TypeOperators, TypeFamilies, GADTs
 , UndecidableInstances, FlexibleContexts, AllowAmbiguousTypes
 , ScopedTypeVariables, TypeApplications, ConstraintKinds #-}

module Control.Api.Adjoint.Monad where

import GHC.Generics

import Data.Functor.Adjunction 
import Data.Typeable

import Control.Applicative

import Control.Monad.Trans.Adjoint
import Control.Monad.Adjoint

import Control.Monad.Free
import Control.Comonad.Cofree

import Control.Comonad.Trans.Env
import Control.Monad.Reader

import Control.Monad.Writer.Lazy
import Control.Comonad.Trans.Traced

-- | Type level api for compos and combinate adjunctions in adjoints
-- 
-- through type families and type operators maybe controll adjunctor structur 
-- for serach, adding, combinate under AdjVar with upper AdjVar
--
-- for exemple:
--
-- > adjF1G1 :: AdjointApiM api1 m a
-- > adjF2G2 :: AdjointApiM api2 m a
-- >
-- > compAdjF2F1G1G2 :: AdjointApiM (api1 :..: api2) m (a,b)
-- > combAdjF1F2G1G2 :: AdjointApiM (api1 :+*: api2) m (Either a b)
-- >
-- > adjF1G1 ## adjF2G2 = compAdjF2F1G1G2 
-- > adjF1G1 +* adjF2G2 = combAdjF1F2G1G2
class Adjunction (FAdjVar api) (GAdjVar api) => AdjVar api where
  -- | Left adjunctor with associated type families for type level adjoint api
  type FAdjVar api :: * -> *
  -- | Right adjunctor with associated type families for type level adjoint api
  type GAdjVar api :: * -> *

type AdjointApiT api = AdjointT (FAdjVar api) (GAdjVar api)

instance (AdjVar ap1, AdjVar api2
	, Adjunction (FAdjVar api1) (GAdjVar api1)
	, Adjunction (FAdjVar api2) (GAdjVar api2)
	) => AdjVar (api1 :..: api2) where
  -- | Compos two Left adjunctors, sequence rigth on left
  type FAdjVar (api1 :..: api2) = (FAdjVar api2 :.: FAdjVar api1)
  -- | Compos two Right adjunctors, sequence is same 
  type GAdjVar (api1 :..: api2) = (GAdjVar api1 :.: GAdjVar api2)

instance (AdjVar ap1, AdjVar api2
	, Adjunction (FAdjVar api1) (GAdjVar api1)
	, Adjunction (FAdjVar api2) (GAdjVar api2)
	) => AdjVar (api1 :+*: api2) where
  -- | Combinate two Left adjunctors in sum
  type FAdjVar (api1 :+*: api2) = (FAdjVar api1 :+: FAdjVar api2)
  -- | Combinate two Right adjunctors in product
  type GAdjVar (api1 :+*: api2) = (GAdjVar api1 :*: GAdjVar api2)

-- | Type level compos adjunctors
data a :..: b = CompAdj a b

-- | Type level combin adjunctors
data a :+*: b = Comb a b 

-- | Cxt for cuts, 
-- contains AdjVar, Typeable, Adjunction, Monad for parametors
type CxtAdjointApiM api1 api2 m a b = (AdjVar api1, Typeable api1, AdjVar api2, Typeable api2
	, Typeable a, Typeable b
	, Adjunction (FAdjVar api1) (GAdjVar api1)
	, Adjunction (FAdjVar api2) (GAdjVar api2)
	, Monad m
	)

-- | GADTs data with type level api for AdjointT
data AdjointApiM api m a  where 
  CompAdjApiM :: CxtAdjointApiM api1 api2 m a b
	=> AdjointApiM api1 m a -> AdjointApiM api2 m b -> AdjointApiM (api1 :..: api2) m (a,b)
  CombAdjApiM :: CxtAdjointApiM api1 api2 m a b
	=> AdjointApiM api1 m a -> AdjointApiM api2 m b -> AdjointApiM (api1 :+*: api2) m (Either a b)
  AdjApiM :: AdjointT (FAdjVar api) (GAdjVar api) m a -> AdjointApiM api m a
{-
liftAdj :: CxtAdjointApiM api1 api2 m a b
	=> Proxy (api1,api2) -> AdjointT (FAdjVar api1) (GAdjVar api1) m a -> AdjointApiM api2 m b -> Maybe (AdjointApiM api2 m (a,b) )
liftAdj (p :: Proxy (api1,api2)) (adj1 :: AdjointT (FAdjVar api1) (GAdjVar api1) m a) (AdjApiM (adj2 :: AdjointT (FAdjVar api2) (GAdjVar api2) m b )) = do
	eqT @api1 @api2
	eqT @(AdjointT (FAdjVar api1) (GAdjVar api1) m a) @(AdjointT (FAdjVar api2) (GAdjVar api2) m b )
	eqT @(GAdjVar api1) @(GAdjVar api2)
	v <- cast adj1
	return $ AdjApiM $ adj2 >>= (\x-> (\y-> (y,x)) <$> v)
liftAdj (p :: Proxy (api1,api2)) (adj1 :: AdjointT (FAdjVar api1) (GAdjVar api1) m a) 
	(CompAdjApiM adj2' adj3' ) =
	( (\x-> CompAdjApiM x adj3 ) <$> liftAdj (Proxy :: Proxy (api1,api2) ) adj1 adj2 
	) <|> (
	(\x-> CompAdjApiM adj2 x ) <$> liftAdj (Proxy :: Proxy (api1,api2) ) adj1 adj3)
liftAdj (p :: Proxy (api1,api2)) (adj1 :: AdjointT (FAdjVar api1) (GAdjVar api1) m a) 
	(CombAdjApiM (adj2 :: AdjointApiM api2 m x ) (adj3 :: AdjointApiM api3 m y )) =
	((\x-> CombAdjApiM x adj3) <$> liftAdj (Proxy :: Proxy (api1,api2) ) adj1 adj2 
	) <|> ((\x-> CombAdjApiM adj2 x) <$> liftAdj (Proxy :: Proxy (api1,api2) ) adj1 adj3)
-}

-- | Operator for compos two AdjointApiM
(##) :: CxtAdjointApiM api1 api2 m a b
	=> AdjointApiM api1 m a -> AdjointApiM api2 m b -> AdjointApiM (api1 :..: api2) m (a,b)
(##) = CompAdjApiM 

-- | Operator for combin two AdjointApiM
(+*) :: CxtAdjointApiM api1 api2 m a b
	=> AdjointApiM api1 m a -> AdjointApiM api2 m b -> AdjointApiM (api1 :+*: api2) m (Either a b)
(+*) = CombAdjApiM 

-- | Compile tree AdjointApiM to one AdjointT
compilAdjApiM :: (AdjVar api, Typeable api, Typeable a, Adjunction (FAdjVar api) (GAdjVar api), Monad m)
  => Proxy (api,a) ->  AdjointApiM api m a -> Maybe (AdjointT (FAdjVar api) (GAdjVar api) m a)
compilAdjApiM _ (AdjApiM a) = return a
compilAdjApiM (Proxy :: Proxy (api,x)) (CompAdjApiM (a1 :: AdjointApiM api1 m a) (a2 :: AdjointApiM api2 m b) :: AdjointApiM api m x ) = do
	eqT @(api1 :..: api2) @api
	eqT @x @(a,b)
	v1 <- compilAdjApiM (Proxy :: Proxy (api1,a)) a1
	v2 <- compilAdjApiM (Proxy :: Proxy (api2,b)) a2
	return $ compAdjoint v1 v2
compilAdjApiM (Proxy :: Proxy (api,x)) (CombAdjApiM (a1 :: AdjointApiM api1 m a) (a2 :: AdjointApiM api2 m b) :: AdjointApiM api m x) = do
	eqT @(api1 :+*: api2) @api
	eqT @x @(Either a b)
	v1 <- compilAdjApiM (Proxy :: Proxy (api1,a)) a1
	v2 <- compilAdjApiM (Proxy :: Proxy (api2,b)) a2
	return $ combAdjoint v1 v2

data AdjEnv a api = AdjEnv a api

data AdjEvent e api = AdjEvent e api

data AdjInterpre api = AdjInterpre api

-- | AdjEnv enviroment AdjVar 
instance (AdjVar api
	, Adjunction (FAdjVar api) (GAdjVar api)
	) => AdjVar (AdjEnv v api) where
  type FAdjVar (AdjEnv v api) = (EnvT v (FAdjVar api))
  type GAdjVar (AdjEnv v api) = (ReaderT v (GAdjVar api))

instance (AdjVar api
	, Adjunction (FAdjVar api) (GAdjVar api)
	) => AdjVar (AdjEvent v api) where
  type FAdjVar (AdjEvent v api) = (WriterT v (FAdjVar api))
  type GAdjVar (AdjEvent v api) = (TracedT v (GAdjVar api))
 
instance (AdjVar api
	, Adjunction (FAdjVar api) (GAdjVar api)
	) => AdjVar (AdjInterpre api) where
  type FAdjVar (AdjInterpre api) = (Free (FAdjVar api))
  type GAdjVar (AdjInterpre api) = (Cofree (GAdjVar api))

