{-# OPTIONS --cubical --safe #-}

module SDG.Infinitesimals.Base where


  open import Cubical.Foundations.Everything
  open import Cubical.Algebra.Algebra
  open import Cubical.Data.Sigma
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_ ; _^_ to _^ℕ_ )
  open import Cubical.Data.FinData
  
  open import Cubical.Algebra.Ring
  
  open import Cubical.Algebra.Ring.Kernel
  open import Cubical.Algebra.CommRing.Ideal renaming (IdealsIn to IdealsInRing)
  open import Cubical.Algebra.Ring.Ideal
  open import Cubical.Algebra.CommRing.FGIdeal
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Module
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
  open import Cubical.HITs.SetQuotients
  open import Cubical.HITs.PropositionalTruncation
  open import Cubical.Foundations.Powerset renaming (_∈_ to _∈p_)
  open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
  open import Cubical.Relation.Nullary
  open import Cubical.Algebra.CommRingSolver.Utility

  open import SDG.Base
  open import SDG.WeilAlgebra.Base

  module RingSpectrum (ℝ@(R , str) : CommRing ℓ) where

    Spec : (A : CommRing ℓ) → Type ℓ
    Spec A = CommRingHom A ℝ

  module AlgebraSpectrum (ℝ@(R , str) : CommRing ℓ) where

    open BasicInstances ℝ
    Spec : (X : CommAlgebra ℝ ℓ) → Type ℓ
    Spec X = CommAlgebraHom X A

  module InfinitesimalType (ℝ@(R , str) : CommRing ℓ) where

    open AlgebraSpectrum ℝ
    open WeilAlgebraDef ℝ
    InfType : Type (ℓ-suc ℓ)
    InfType = Σ[ X ∈ Type ℓ ] Σ[ W ∈ WeilAlgebra ] Iso X (Spec (W .fst .fst))