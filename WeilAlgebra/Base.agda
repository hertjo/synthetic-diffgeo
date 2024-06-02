{-# OPTIONS --cubical --safe #-}

module SDG.WeilAlgebra.Base where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.Nat
  open import Cubical.Data.Sigma
  open import Cubical.Data.Bool
  open import Cubical.Data.FinData
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.Ring.BigOps
  open import Cubical.Algebra.CommRing.FGIdeal
  open import Cubical.Algebra.Module
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.Kernel
  open import Cubical.Algebra.CommAlgebra.Ideal
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.HITs.PropositionalTruncation
  open import Cubical.Foundations.Powerset
  open import SDG.Base
  open import SDG.WeilAlgebra.Instances
  open import SDG.Infinitesimals.Instances


  module WeilAlgebraDef (ℝ@(R , str) : CommRing ℓ) where
    
    -- We can consider that a Weil algebra is merely equivalent to an algebra of the form 
    -- ℝ[I]/(FGIdeal), with augmentation xᵢ → 0.
      open BasicInstances ℝ
      augmentedCommAlgebra : Type (ℓ-suc ℓ)
      augmentedCommAlgebra = Σ (CommAlgebra ℝ ℓ) λ X → CommAlgebraHom X A
      augmentationIdeal : (X : augmentedCommAlgebra) → IdealsIn (fst X)
      augmentationIdeal X = kernel (fst X) A (snd X)
      isFGIdeal : (X : CommAlgebra ℝ ℓ)(I : IdealsIn X) → Type (ℓ-suc ℓ)
      isFGIdeal X I = Σ (FGIdealIn (CommAlgebra→CommRing X)) λ H → (x : ⟨ X ⟩) → Iso (x ∈ fst I) (x ∈ fst (fst H))
      augIdealIsNilpotent : (X : augmentedCommAlgebra) → Type ℓ
      augIdealIsNilpotent X = CommIdealUtils.isNilpotent (CommAlgebra→CommRing (fst X)) (augmentationIdeal X)
      augIdealIsFGIdeal : (X : augmentedCommAlgebra) → Type (ℓ-suc ℓ)
      augIdealIsFGIdeal X = ∥ isFGIdeal (fst X) (augmentationIdeal X) ∥₁
      isWeilAlgebra : (X : augmentedCommAlgebra) → Type (ℓ-suc ℓ)
      isWeilAlgebra X = (augIdealIsNilpotent X) × (augIdealIsFGIdeal X)
      WeilAlgebra : Type (ℓ-suc ℓ)
      WeilAlgebra = Σ augmentedCommAlgebra (λ X → isWeilAlgebra X)
      
      open 1Disk ℝ
      open 1DFundamentalWeilAlgebras ℝ
      open 1DFreeCommAlgebraUtils ℝ
      ev0 : (n : ℕ) → CommAlgebraHom (W n) A
      ev0 n = Iso.inv (FPHomIso 1 (var-power n)) (0d A n)  

      augW : (n : ℕ) → augmentedCommAlgebra
      augW n = (W n) , (ev0 n) 

      -- open Product
      -- augWIsNilpotent : (n : ℕ) → augIdealIsNilpotent (augW n)
      -- augWIsNilpotent zero = ∣ 1 , (λ x → ∏ (CommRing→Ring (CommAlgebra→CommRing (W zero))) (λ k → fst (x k)) ≡⟨ refl ⟩ ((snd (W zero)) CommAlgebraStr.· fst (x zero)) {!   !} ≡⟨ {!   !} ⟩ {!   !} ≡⟨ {!   !} ⟩ {!   !} ∎) ∣₁
      -- augWIsNilpotent (suc n) = ∣ suc (suc n) , {!   !} ∣₁
      

      -- record WeilAlgebra (W : augmentedCommAlgebra) : Type {!   !} where
      --   field


  --     open BasicInstances ℝ
  --     open 1DFreeCommAlgebraUtils ℝ
  --     open ModuleUtils ℝ
  --     open 1DFundamentalWeilAlgebras ℝ
  --     open CommIdealUtils (CommAlgebra→CommRing (W n))
  --     open commonExtractors
  --     open import Cubical.Algebra.CommAlgebra.Ideal
    
  --     weilAlgebraProperty : (X : CommAlgebra ℝ ℓ) → Type (ℓ-suc ℓ)
  --     weilAlgebraProperty X = Σ[ N ∈ nilpotentIdeal ] Iso ⟨ Algebra→Module (CommAlgebra→Algebra X) ⟩ ⟨ A⊕ N ⟩ --Σ[ N ∈ nilpotentIdeal ] Iso ⟨ Algebra→Module (CommAlgebra→Algebra X) ⟩ ⟨ A⊕ ? ⟩
  --       where
  --         reclift : (n : ℕ) → Lift {ℓ-zero} {ℓ} (Fin n) → Fin n
  --         reclift n (lift i) = i
  --         A⊕ : (N : nilpotentIdeal) → LeftModule (CommRing→Ring (CommAlgebra→CommRing (W n))) ℓ
  --         A⊕ N = pointwiseModule (CommAlgebra→CommRing (W n)) {X = Lift (Fin 2)} 
  --                   (λ k →  CommIdeal→LeftModule (CommAlgebra→CommRing (W n)) 
  --                     (if (reclift 2 k) == zero 
  --                       then 
  --                         1Ideal (W n)
  --                       else 
  --                         (fst N)))

  --     isWeilAlgebra : (X : CommAlgebra ℝ ℓ) → Type (ℓ-suc ℓ)
  --     isWeilAlgebra X = ∥ weilAlgebraProperty X ∥₁ 

  --     isFPWeilAlgebra : Σ[ X ∈ CommAlgebra ℝ ℓ ] isFPAlgebra X → Type (ℓ-suc ℓ)
  --     isFPWeilAlgebra X = isWeilAlgebra (fst X) 

  -- module 1DFundamentalWeilAlgebrasProperties (ℝ@(R , str) : CommRing ℓ) (n : ℕ) where

  --   open Definition ℝ
  --   open 1DFundamentalWeilAlgebras ℝ
  --   open 1DFreeCommAlgebraUtils ℝ
  --   open BasicInstances ℝ

  --   -- mainThm : isWeilAlgebra ℝ n (W n)
  --   -- mainThm = ∣ (genIdeal {n = 1} (CommAlgebra→CommRing (W n)) (λ _ → eps₀ n) , ∣ (suc n) , (λ x → {!   !}) ∣₁) ,
  --   --            iso (λ x k → if (reclift 2 k) == zero 
  --   --                     then 
  --   --                       {!   !} , {!   !}
  --   --                     else 
  --   --                       {!   !}) {!   !} {!   !} {!   !} ∣₁
     
  --   --   where
  --   --     reclift : (n : ℕ) → Lift {ℓ-zero} {ℓ} (Fin n) → Fin n
  --   --     reclift n (lift i) = i    