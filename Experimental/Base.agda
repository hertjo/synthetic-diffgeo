
{-# OPTIONS --cubical #-}

module SDG.Experimental.Base where

    open import Cubical.Foundations.Everything
    open import Cubical.Algebra.CommRing  
    open import Cubical.Relation.Nullary
    open import Cubical.Data.Sigma
    open import Cubical.Data.Nat
    open import Cubical.Data.Unit
    open import Cubical.Data.FinData
    open import Cubical.Data.Bool
    open import Cubical.Algebra.CommRing.Instances.Unit
    open import Cubical.Algebra.CommRing.Instances.Pointwise
    

    variable
        ℓ : Level


    module _ (ℝ@(R , str) : CommRing ℓ) where

        ℕ< : (n : ℕ) → Type ℓ
        ℕ< n = Lift (Fin n)

        big∧ : (n : ℕ) → (Fin n → Type ℓ) → Type ℓ
        big∧ zero X = Lift Unit
        big∧ (suc n) X = big∧ n (λ k → X (fromℕ {!   !})) × (X (fromℕ n))
        --big∨
        realSpace : (n : ℕ) → CommRing ℓ
        realSpace n =  pointwiseRing (ℕ< n) ℝ

    module _ (ℝ@(R , str) : CommRing ℓ) where
        open CommRingStr str
        -- Synthetic Differential Geometry axioms from David Jaz Myers paper on orbifolds, defining the smooth real line ℝ.
        postulate
            -- Postulate K: ℝ is a field in the sense of Kock:
            postulateK : (¬ 0r ≡ 1r) × ((n : ℕ) → (x : ⟨ realSpace ℝ n ⟩) → 
                        ¬ {! __  !} → {!  _∧_ !})

    
 