{-# OPTIONS --cubical --safe #-}

module SDG.WeilAlgebra.Instances where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.Nat
  open import Cubical.Data.FinData
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.HITs.PropositionalTruncation
  open import SDG.Base

  module 1DFundamentalWeilAlgebras (ℝ@(R , str) : CommRing ℓ) where

    open 1DFreeCommAlgebraUtils ℝ
  
    W : (n : ℕ) → CommAlgebra ℝ ℓ
    W n = FPAlgebra {ℓ} {ℝ} {1} 1 (var-power n)
    eps : (n : ℕ) (i : Fin 1) → ⟨ W n ⟩
    eps n i = generator 1 (var-power n) i
    eps₀ : (n : ℕ) → ⟨ W n ⟩
    eps₀ n = eps n zero

    -- <ε> : {! CommIdeal ℝ !}
    -- <ε> = {!   !}
    -- WIsWeilAlgebra : (n : ℕ) → isWeilAlgebra (W n)
    -- WIsWeilAlgebra n = ∣ (<ε> , {!   !}) , {!   !} ∣₁


  
