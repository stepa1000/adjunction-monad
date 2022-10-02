{-# Language TypeOperators, TypeFamilies #-}

module Control.Monad.Adjoint where

import GHC.Generics

import Data.Functor.Adjunction

import Control.Monad.Trans.Adjoint

compAdjoint ::(Adjunction f g, Adjunction f2 g2, Monad m)
	=> AdjointT f g m a -> AdjointT f2 g2 m b -> AdjointT (f2 :.: f) (g :.: g2) m (a,b)
compAdjoint (AdjointT a1) (AdjointT a2) = AdjointT $
	(fmap . fmap) Comp1 $
	Comp1 $ 
	fmap (\x->fmap ((>>= (\y-> (\y2->((\z->(\x2->(x2,z)) <$> y2 ) <$>y)) <$> x)) ) a2 ) a1


combAdjoint :: (Adjunction f g, Adjunction f2 g2, Monad m)
	=> AdjointT f g m a -> AdjointT f2 g2 m b -> AdjointT (f :+: f2) (g :*: g2) m (Either a b)
combAdjoint (AdjointT a1) (AdjointT a2) = AdjointT $ 
	((fmap . fmap) (L1 . fmap Left) a1) :*: 
	((fmap . fmap) (R1 . fmap Right) a2)
