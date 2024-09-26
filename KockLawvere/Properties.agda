

{-# OPTIONS --cubical #-}

module SDG.KockLawvere.Properties where

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
  open import SDG.Infinitesimals.Instances
  open import SDG.KockLawvere.Base

  module Derivative (ℝ@(R , str) : CommRing ℓ) where

    open BasicInstances ℝ
    open FreeCommAlgebraUtils ℝ
    open 1DFreeCommAlgebraUtils ℝ
    open 1DFundamentalWeilAlgebras ℝ
    open AlgebraSpectrum ℝ
    open Axiom ℝ
    open Construction ℝ
    
    d/dε : (n : ℕ) → ⟨ W (suc n) ⟩ → ⟨ W n ⟩
    d/dε n x = transport (sym (link n)) (pred/dε n x)
      where
        link : (n : ℕ) → ⟨ W n ⟩ ≡ ⟨ FPAlgebra2 1 (var-power (suc n)) (var-power n) ⟩
        link n = makeFP1Char 1 (var-power n) ∙ (sym (makeFP2Char 1 (var-power (suc n)) (var-power n)))
        pred/dε : (n : ℕ) → ⟨ W (suc n) ⟩ → ⟨ FPAlgebra2 1 (var-power (suc n)) (var-power n) ⟩
        pred/dε n = makeFPMap2 1 (var-power (suc n)) (var-power n) d/dξ help1
          where
            lc = linearCombination R[ξ]
            derivReducesDeg : (a b : ⟨ A[ξ] ⟩) → Type ℓ
            derivReducesDeg a b = ∥ Σ (FinVec ⟨ A[ξ] ⟩ 1) (λ x → ((d/dξ a) + (- (d/dξ b))) ≡ linearCombination R[ξ] x (var-power n)) ∥₁

            help1 : (a b : ⟨ A[ξ] ⟩) → ((a + (- b)) ∈ fst (relationsIdeal 1 (var-power (suc n)))) → 
                    derivReducesDeg a b
            help1 a b r = map decreaseDeg r
              where
                decreaseDeg : Σ (FinVec ⟨ Polynomials 1 ⟩ 1) (λ x → (a + (- b)) ≡ linearCombination R[ξ] x (var-power (suc n))) → 
                            Σ (FinVec ⟨ Polynomials 1 ⟩ 1) λ x → (d/dξ a + (- (d/dξ b))) ≡ linearCombination R[ξ] x (var-power n)
                decreaseDeg H = factor , 
                                ((d/dξ a + (- d/dξ b))                                                                                                    ≡⟨ refl ⟩ 
                                d/dξ (a + (- b))                                                                                                          ≡⟨ cong (λ z → d/dξ z) (snd H) ⟩
                                d/dξ (linearCombination R[ξ] (fst H) (var-power (suc n)))                                                                 ≡⟨ refl ⟩
                                d/dξ (((fst H zero) · (var-power (suc n) zero)) + 0a)                                                                     ≡⟨ cong (λ z → d/dξ z) (+-rid ((fst H zero) · (var-power (suc n) zero))) ⟩
                                d/dξ ((fst H zero) · (var-power (suc n) zero))                                                                            ≡⟨ refl ⟩
                                (((d/dξ (fst H zero)) · (var-power (suc n) zero)) + ((fst H zero) · (d/dξ (var-power (suc n) zero))))                     ≡⟨ refl ⟩
                                (((d/dξ (fst H zero)) · ((ξ zero) · (var-power n zero))) + ((fst H zero) · (d/dξ (var-power (suc n) zero))))              ≡⟨ cong (λ z → z + ((fst H zero) · (d/dξ (var-power (suc n) zero)))) (·-assoc (d/dξ (fst H zero)) (ξ zero) (var-power n zero)) ⟩
                                (expr + ((fst H zero) · (d/dξ (var-power (suc n) zero))))                                                                 ≡⟨ cong (λ z → expr + ((fst H zero) · z)) helper1 ⟩
                                (expr + ((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · (exp A[ξ] (ξ zero) (suc n) · d/dξ (ξ zero)))))        ≡⟨ refl ⟩
                                (expr + ((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · (var-power n zero · d/dξ (ξ zero)))))                           ≡⟨ cong (λ z → expr + ((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · z))) (·-comm (var-power n zero) (d/dξ (ξ zero))) ⟩
                                (expr + ((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · (d/dξ (ξ zero) · var-power n zero))))                           ≡⟨ cong (λ z → expr + ((fst H zero) · z)) (·-assoc (embedℕinAlg A[ξ] (suc (suc n))) (d/dξ (ξ zero)) (var-power n zero)) ⟩
                                (expr + ((fst H zero) · ((embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero)) · var-power n zero)))                           ≡⟨ cong (λ z → expr + z) (·-assoc (fst H zero) (embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero)) (var-power n zero)) ⟩
                                (expr + (((fst H zero) · (embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero))) · var-power n zero))                           ≡⟨ sym (ldist (d/dξ (fst H zero) · ξ zero) (fst H zero · (embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero))) (var-power n zero)) ⟩
                                (((d/dξ (fst H zero) · ξ zero) +  (fst H zero · (embedℕinAlg A[ξ] (suc (suc n)) · d/dξ (ξ zero)))) · var-power n zero)    ≡⟨ cong (λ z → ((d/dξ (fst H zero) · ξ zero) +  (fst H zero · z)) · var-power n zero) ((·-comm (embedℕinAlg A[ξ] (suc (suc n))) (d/dξ (ξ zero))) ∙ (·-lid (embedℕinAlg A[ξ] (suc (suc n))))) ⟩
                                (((d/dξ (fst H zero) · ξ zero) +  (fst H zero · (embedℕinAlg A[ξ] (suc (suc n))))) · var-power n zero)                    ≡⟨ cong (λ z → ((d/dξ (fst H zero) · ξ zero) +  z) · var-power n zero) (·-comm (fst H zero) (embedℕinAlg A[ξ] (suc (suc n)))) ⟩
                                (((d/dξ (fst H zero) · ξ zero) +  ((embedℕinAlg A[ξ] (suc (suc n))) · fst H zero)) · var-power n zero)                    ≡⟨ sym (+-rid (factor zero · var-power n zero)) ⟩
                                linearCombination R[ξ] factor (var-power n) ∎)
                  where
                    open AlgebraUtils ℝ
                    expr = (d/dξ (fst H zero) · (ξ zero)) · (var-power n zero)
                    helper1 : d/dξ (var-power (suc n) zero) ≡ (embedℕinAlg A[ξ] (suc (suc n)) · (exp A[ξ] (ξ zero) (suc n) · d/dξ (ξ zero)))
                    helper1 = derivPowerRuleVar (suc n) 
                    factor : FinVec ⟨ Polynomials 1 ⟩ 1
                    factor = λ _ → (d/dξ (fst H zero) · ξ zero) +  ((embedℕinAlg A[ξ] (suc (suc n))) · fst H zero)

    open 1Disk ℝ
    factCoeff : (n : ℕ) → ⟨ W n ⟩ → ⟨ A ⟩
    factCoeff zero p = evPolyInfinitesimal zero A p (λ x → 0d A zero)
    factCoeff (suc n) p = factCoeff n (d/dε n p)

    private
      D : ℕ → Type ℓ
      D n = Spec (W n)

    approx1D :  (n : ℕ) → (f : ⟨ A ⟩ → ⟨ A ⟩)(x : ⟨ A ⟩) → D n → ⟨ A ⟩
    approx1D n f a = λ d → f (((snd A) CommAlgebraStr.+ a) (fromZeroLocus₁ 1 (var-power n) A (FPIso d) zero))
      where
        FPIso = Iso.fun (FPHomIso  1 (var-power n))

    Taylor : (n : ℕ) → (f : ⟨ A ⟩ → ⟨ A ⟩)(x : ⟨ A ⟩) → ⟨ W n ⟩
    Taylor n f a = canonicalInv n (approx1D n f a)

    d/dx : (n : ℕ) → (f : ⟨ A ⟩ → ⟨ A ⟩) → ⟨ A ⟩ → ⟨ A ⟩
    d/dx n f a = factCoeff n (Taylor n f a)


    open import Cubical.Data.Bool

    approxND : (n k : ℕ) → Fin n → (⟨ A^ n ⟩ → ⟨ A ⟩) → ⟨ A^ n ⟩ → D k → ⟨ A ⟩
    approxND n k j f v = λ d → f (λ i → 
                                        if reclift n i == j 
                                        then 
                                            ((snd A) CommAlgebraStr.+ (v i)) (fromZeroLocus₁ 1 (var-power k) A (FPIso d) zero) 
                                        else v i)
      where
        FPIso = Iso.fun (FPHomIso 1 (var-power k))
        reclift : (n : ℕ) → Lift (Fin n) → Fin n
        reclift n (lift i) = i
    

    ∂/∂x : (n k : ℕ) → Fin n → (⟨ A^ n ⟩ → ⟨ A ⟩) → ⟨ A^ n ⟩ → ⟨ A ⟩
    ∂/∂x n k j f v = factCoeff k (canonicalInv k (approxND n k j f v))
    
    -- T : (f : ⟨ A ⟩ → ⟨ A ⟩)(a : ⟨ A ⟩) → Type ℓ
    -- T f a = Σ[ y ∈ ⟨ A ⟩ ] {!   !} 