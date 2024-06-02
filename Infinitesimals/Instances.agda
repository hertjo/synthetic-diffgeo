
{-# OPTIONS --cubical --safe #-}

module SDG.Infinitesimals.Instances where

  open import Cubical.Foundations.Everything

  open import Cubical.Data.Nat
  open import Cubical.Data.FinData
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Relation.Nullary
  open import Cubical.Algebra.CommRingSolver.Utility
  open import Cubical.HITs.PropositionalTruncation
  
  open import SDG.Base
  open import SDG.WeilAlgebra.Instances

  module 1Disk (ℝ@(R , str) : CommRing ℓ) where
  
    -- / The disk of order n is the zero locus of the generator of the quotient algebra A[ξ]/(ξ^n), which is isomorphic to 
    -- / Spec(X) := CommAlgebraHom X A (where A is ℝ as algebra)

    open 1DFreeCommAlgebraUtils ℝ
    open AlgebraUtils ℝ
  
    infDskOfOrder : (A : CommAlgebra ℝ ℓ)(n : ℕ) → Type ℓ
    infDskOfOrder A n = zeroLocus 1 (var-power n) A 

    infDskOfOrder∞ : (A : CommAlgebra ℝ ℓ) → Type ℓ
    infDskOfOrder∞ A = Σ[ n ∈  ℕ ] infDskOfOrder A n

    -- infDskOfOrder∞' : (A : CommAlgebra ℝ ℓ) → Type ℓ
    -- infDskOfOrder∞' A = Σ[ d ∈  ⟨ A ⟩ ] Σ[ n ∈ ℕ ] evPoly A (var-power {! n  !} zero) (λ _ → d) ≡ CommAlgebraStr.0a (snd A)

    
    -- ?
    -- infDsksIso : (A : CommAlgebra ℝ ℓ) → Iso (infDskOfOrder∞ A) (infDskOfOrder∞' A)
    -- Iso.fun (infDsksIso A) x = {!   !} , (fst x) , fromZeroLocus₂ 1 (var-power (fst x)) A (snd x) zero
    --   --where
    --     -- p1 :  {!   !}
    --     -- p1 = fromZeroLocus₁ 1 (var-power {!   !}) A {!   !} zero
    --     -- p2 :  evPoly A (var-power {!   !} zero) (fromZeroLocus₁ 1 (var-power (fst x)) A (snd x)) ≡ CommAlgebraStr.0a (snd A)
    --     -- p2 = fromZeroLocus₂ 1 (var-power (fst x)) A (snd x) zero
    -- Iso.inv (infDsksIso A) x = {!   !}
    -- Iso.inv (infDsksIso A) = {!   !}
    -- Iso.rightInv (infDsksIso A) = {!   !}
    -- Iso.leftInv (infDsksIso A) = {!   !}

    0d : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder A n
    0d A n = makeZeroLocusTerm 1 (var-power n) A (λ _ → 0a) λ i → 
              evPoly A (gen (suc n)) (λ _ → 0a)                   ≡⟨ evPolyChar A (suc n) (λ _ → 0a) ⟩ 
              exp A 0a (suc n)                                    ≡⟨ refl ⟩ 
              ((snd A) CommAlgebraStr.· 0a) (exp A 0a n)          ≡⟨ RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A)) (exp A 0a n) ⟩ 
              0a  ∎
           
      where
        open CommAlgebraStr (snd A)

    incl : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder A n → infDskOfOrder∞ A
    incl A n d = n , d

    retr : (A : CommAlgebra ℝ ℓ)(n : ℕ) → infDskOfOrder∞ A → infDskOfOrder A n
    retr A n (m , d) with discreteℕ m n
    ... | yes p = transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc (p i))) A) d
    ... | no ¬p = 0d A n

    isRetrRetr : (k : ℕ)(A : CommAlgebra ℝ ℓ) → (d : infDskOfOrder A k) → (retr A k ∘ (incl A k)) d ≡ d
    isRetrRetr k A d with discreteℕ k k 
    ... | yes p = transport zeroLocusPath d           ≡⟨ step1 ⟩ 
                  transport zeroLocusPathEndpoint d   ≡⟨ step2 ⟩ 
                  d  ∎
      where
        congZeroLocus = cong (λ a → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc a)) A)
        zeroLocusPath = λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc (p i))) A
        zeroLocusPathEndpoint = λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc k)) A
        step1 = cong (λ a → transport a d) (λ i → congZeroLocus (isSetℕ k k p refl i))
        step2 = transportRefl d
    ... | no ¬p = byAbsurdity (¬p refl)    

    open 1DFundamentalWeilAlgebras ℝ
    open BasicInstances ℝ
    evPolyInfinitesimal : (n : ℕ) → (A : CommAlgebra ℝ ℓ) → ⟨ W n ⟩ → FinVec (infDskOfOrder A n) 1 → ⟨ A ⟩
    evPolyInfinitesimal n A P values = (fst (inducedHomFP 1 (var-power n) A (values zero))) P  -- fst (freeInducedHom A values) P
    
    evPolyInf : (n : ℕ) → ⟨ A[ξ] ⟩ → FinVec (infDskOfOrder A n) 1 → ⟨ A ⟩
    evPolyInf n P val = evPolyInfinitesimal n A ((fst (modRelations 1 (var-power n))) P) val


    -- Experimental ----------------------------------------------------------

    -- d^k+1≡0 : (k : ℕ)(A : CommAlgebra ℝ ℓ)(d : ⟨ A ⟩) → Type ℓ
    -- d^k+1≡0 n A d = evPoly A (var-power n zero) (λ _ → d) ≡ 0a
    --   where
    --       open CommAlgebraStr (snd A)

    -- nilp : (A : CommAlgebra ℝ ℓ)(d : ⟨ A ⟩) → Type ℓ
    -- nilp A d = Σ[ n ∈ ℕ ] d^k+1≡0 n A d
    
    -- D : (A : CommAlgebra ℝ ℓ) → Type ℓ
    -- D A = Σ[ d ∈  ⟨ A ⟩ ] ∥ nilp A d ∥₁

    -- map1 : (A : CommAlgebra ℝ ℓ)(d : ⟨ A ⟩) → ((n , dNilp) : nilp A d) → d^k+1≡0 n A d
    -- map1 A d P = snd P

  
    --map3 : (A : CommAlgebra ℝ ℓ) → ((d , P) : D A) → nilp A d
    --map3 A d = _ , Cubical.HITs.PropositionalTruncation.rec (isSetCommAlgebra A (evPoly A (var-power _ zero) (λ _ → fst d)) (CommAlgebraStr.0a (snd A))) (map1 A (fst d)) (snd d)
    -- pre∞iDO : (A : CommAlgebra ℝ ℓ) → Type ℓ
    -- pre∞iDO A = Σ[ d ∈  ⟨ A ⟩ ] (Σ[ n ∈ ℕ ] evPoly A (var-power n zero) (λ _ → d) ≡ CommAlgebraStr.0a (snd A))

    -- iDO : (n : ℕ)(A : CommAlgebra ℝ ℓ) → Type ℓ
    -- iDO n A = Σ[ d ∈  ⟨ A ⟩ ] evPoly A (var-power n zero) (λ _ → d) ≡ CommAlgebraStr.0a (snd A)

    -- prop1 : (A : CommAlgebra ℝ ℓ) → ∞iDO A → infDskOfOrder∞ A
    -- prop1 A d = n , (makeZeroLocusTerm 1 (var-power n) A (λ x → d) λ i → p)
 