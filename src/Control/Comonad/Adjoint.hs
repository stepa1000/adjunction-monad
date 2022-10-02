{-# Language TypeOperators #-}

module Control.Comonad.Adjoint where

import GHC.Generics

import Data.Functor.Adjunction
import Data.Maybe

import Control.Comonad.Trans.Adjoint

import Control.Comonad

compAdjoint :: (Adjunction f g, Adjunction f2 g2, Comonad w, ComonadApply w, Functor g)
	=> AdjointT f g w a -> AdjointT f2 g2 w b -> AdjointT (f2 :.: f) (g :.: g2) w (a,b)
compAdjoint (AdjointT a1) (AdjointT a2) = AdjointT $ 
	(fmap . fmap) Comp1 $
	Comp1 $ 
	fmap (\x-> fmap (\y-> liftW2 (\t h-> fmap (\a-> fmap (\b-> (a,b) )  t) h) x y )  a1 ) a2

combAdjoint :: (Adjunction f g, Adjunction f2 g2, Comonad w, Functor g)
	=> AdjointT f g w a -> AdjointT f2 g2 w b -> [AdjointT (f :+: f2) (g :*: g2) w (Either a b)]
combAdjoint (AdjointT a1) (AdjointT a2) = [AdjointT $ ((fmap . fmap) (\g-> (fmap Left g) :*: (fmap Right $ extract $ extractL $ a2 ) ) $ L1 a1)] ++
	[AdjointT $ (((fmap . fmap) (\g2-> (fmap Left $ extract $ extractL a1 ) :*: (fmap Right g2)) . R1) a2)]
