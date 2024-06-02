

{-# OPTIONS --cubical #-}

module SDG.KockLawvere.Base where

  open import Cubical.Foundations.Everything renaming (const to consts)
  open import Cubical.Data.FinData
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
  open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra renaming (_[_] to _⟦_⟧)
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_ ; 
                                          +-assoc to +-assocℕ ; +-comm to +-commℕ ;
                                          ·-assoc to ·-assocℕ ; ·-comm to ·-commℕ)
  open import Cubical.Foundations.Powerset
  open import Cubical.Data.Sigma
  open import Cubical.Algebra.Ring.BigOps
  open import Cubical.HITs.SetQuotients renaming (_/_ to _//_)
  open import Cubical.HITs.PropositionalTruncation
  open import Cubical.Data.Fin.LehmerCode 
  open import Cubical.Algebra.CommRing.FGIdeal renaming (generatedIdeal to genIdealRing)
  open import Cubical.Algebra.CommAlgebra.FGIdeal
  open import SDG.Base
  open import SDG.WeilAlgebra.Instances
  open import SDG.Infinitesimals.Base

  module Axiom (ℝ@(R , str) : CommRing ℓ) where

    open BasicInstances ℝ
    open 1DFundamentalWeilAlgebras ℝ
    open AlgebraSpectrum ℝ

    canonicalMap : (n : ℕ) → ⟨ W n ⟩ → (Spec (W n) → ⟨ A ⟩ )
    canonicalMap n p d = fst d p
    postulate
      KLAxiom : (n : ℕ) → isIso (canonicalMap n)
    canonicalInv : (n : ℕ) → (Spec (W n) → ⟨ A ⟩) → ⟨ W n ⟩
    canonicalInv n = fst (KLAxiom n)
    