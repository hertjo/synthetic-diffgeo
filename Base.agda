{-# OPTIONS --cubical --safe #-}

module SDG.Base where

  open import Cubical.Foundations.Everything renaming (const to cons)
  open import Cubical.Data.Sigma
  open import Cubical.Data.FinData
  open import Cubical.Algebra.Ring
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommRing.Ideal
  open import Cubical.Algebra.Ring.Ideal
  open import Cubical.Algebra.CommRing.FGIdeal  
  open import Cubical.Algebra.Module  
  open import Cubical.Algebra.Algebra
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra 
    renaming (inducedHom to freeInducedHom)
  open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_; _^_ to _^ℕ_ ; +-assoc to +-ℕassoc ; +-comm to +-ℕcomm; ·-assoc to ·-ℕassoc; ·-comm to ·-ℕcomm)
  open import Cubical.Algebra.Ring.BigOps
  open import Cubical.Data.Fin.LehmerCode
  open import Cubical.Algebra.CommAlgebra.Instances.Pointwise
  open import Cubical.Foundations.Powerset renaming (_∈_ to _∈p_)
  open import Cubical.HITs.PropositionalTruncation

  variable
    ℓ : Level

  module GeneralUtils {ℓ : Level} where
  
    LFin : (n : ℕ) → Type ℓ
    LFin n = Lift (Fin n)

    reclift : (n : ℕ) → LFin n → Fin n
    reclift n (lift i) = i

  module RingUtils (ℝ@(R , str) : CommRing ℓ) where
    open CommRingStr str
    embedℕinRing : ℕ → R
    embedℕinRing zero = 0r
    embedℕinRing (suc n) = (embedℕinRing n) + 1r

    exp : R → ℕ → R
    exp x zero = 1r
    exp x (suc n) = x · (exp x n)

    open Sum (CommRing→Ring ℝ)
    polynomialAt : {n : ℕ} → FinVec R n → R → R
    polynomialAt v a = ∑ (λ i → ((snd ℝ) CommRingStr.· (v i)) (exp a (toℕ i)))

    seriesTruncAt : ℕ → (ℕ → R) → R → R
    seriesTruncAt n v x = ∑ {n} (λ k → ((snd ℝ) CommRingStr.· (v (toℕ k))) (exp x (toℕ k)))

  module CommIdealUtils (ℝ@(R , str) : CommRing ℓ) where

    open CommIdeal ℝ

    CommIdeal→Type : CommIdeal → Type ℓ
    CommIdeal→Type I = Σ R λ p → p ∈ I
    
    nilpotency : CommIdeal → Type ℓ
    nilpotency I = Σ ℕ λ n → (x : FinVec (CommIdeal→Type I) n) → (Product.∏ (CommRing→Ring ℝ) λ k → fst (x k)) ≡ CommRingStr.0r str 
    isNilpotent : CommIdeal → Type ℓ
    isNilpotent I = ∥ nilpotency I ∥₁

    nilpotentIdeal : Type (ℓ-suc ℓ)
    nilpotentIdeal = Σ CommIdeal λ I → isNilpotent I

  module ModuleUtils (baseRing : CommRing ℓ) where

    module _ (ℝ@(R , str) : CommRing ℓ)  where
      open CommIdeal ℝ
      open CommRingStr str
      open CommIdealUtils ℝ

      CommIdeal→LeftModule : CommIdeal → LeftModule (CommRing→Ring ℝ) ℓ
      CommIdeal→LeftModule I = CommIdeal→Type I , 
                                leftmodulestr 
                                  (0r , (isCommIdeal.contains0 (snd I))) 
                                  (λ x y → ((fst x) + (fst y)) , (isCommIdeal.+Closed (snd I) (snd x) (snd y))) 
                                  (λ x → (- (fst x)) , (isIdeal.-closed (snd (CommIdeal→Ideal I)) (snd x))) 
                                  (λ a x → (a · (fst x)) , (isCommIdeal.·Closed (snd I) a (snd x))) 
                                  (makeIsLeftModule 
                                    (isSetΣSndProp (isSetCommRing ℝ) isProp_∈I) 
                                    (λ x y z → proofByFirstComp (+Assoc (fst x) (fst y) (fst z))) 
                                    (λ x → proofByFirstComp (+Rid (fst x))) 
                                    (λ x → proofByFirstComp (+Rinv (fst x)))
                                    (λ x y → proofByFirstComp (+Comm (fst x) (fst y))) 
                                    (λ r s x → proofByFirstComp (sym (·Assoc r s (fst x)))) 
                                    (λ r s x → proofByFirstComp (·Ldist+ r s (fst x))) 
                                    (λ r x y → proofByFirstComp (·Rdist+ r (fst x) (fst y))) 
                                    λ x → proofByFirstComp (·Lid (fst x)))
        where
          isProp_∈I = λ x → ∈-isProp (fst I) x
          proofByFirstComp =  Σ≡Prop isProp_∈I
    

    module _ (ℝ@(R , str) : CommRing ℓ)  where
      pointwiseModule : {X : Type ℓ} → (X → LeftModule (CommRing→Ring ℝ) ℓ) → LeftModule (CommRing→Ring ℝ) ℓ
      pointwiseModule {X} M = ((i : X) → fst (M i)) , 
                                  leftmodulestr 
                                  (λ i → LeftModuleStr.0m (snd (M i))) 
                                  (λ x y i → ((snd (M i)) LeftModuleStr.+ x i) (y i)) 
                                  (λ x i → (LeftModuleStr.- (snd (M i))) (x i)) 
                                  (λ a x i → ((snd (M i)) LeftModuleStr.⋆ a) (x i)) 
                                  (makeIsLeftModule 
                                    (isSetΠ (λ i → isSetLeftModule (M i))) 
                                    (λ x y z → funExt (λ i → LeftModuleStr.+-assoc (snd (M i)) (x i) (y i) (z i))) 
                                    (λ x →     funExt (λ i →  LeftModuleStr.+-rid (snd (M i)) (x i))) 
                                    (λ x →     funExt (λ i →  LeftModuleStr.+-rinv (snd (M i)) (x i)))
                                    (λ x y →   funExt (λ i →  LeftModuleStr.+-comm (snd (M i)) (x i) (y i))) 
                                    (λ r s x → funExt (λ i → LeftModuleStr.⋆-assoc (snd (M i)) r s (x i))) 
                                    (λ r s x → funExt (λ i →  LeftModuleStr.⋆-ldist (snd (M i)) r s (x i))) 
                                    (λ r x y → funExt (λ i → LeftModuleStr.⋆-rdist (snd (M i)) r (x i) (y i))) 
                                    λ x →      funExt (λ i → LeftModuleStr.⋆-lid (snd (M i)) (x i)))
      
    module _ (alg : CommAlgebra baseRing ℓ) where
      private
        crng = CommAlgebra→CommRing alg
        rng = CommRing→Ring crng
      open CommIdeal crng
      CommIdealInAlg→LeftModule : CommIdeal → LeftModule rng ℓ
      CommIdealInAlg→LeftModule = CommIdeal→LeftModule crng

      pointwiseModuleInAlg : {X : Type ℓ} → (X → LeftModule rng ℓ) → LeftModule rng ℓ
      pointwiseModuleInAlg {X} = pointwiseModule crng

  module AlgebraUtils (ℝ@(R , strR) : CommRing ℓ) (ℝAlg@(A , strA) : CommAlgebra ℝ ℓ) where

    open RingUtils (CommAlgebra→CommRing ℝAlg) renaming (exp to expR)
    embedℕinAlg : ℕ → A
    embedℕinAlg n = embedℕinRing n
    exp : A → ℕ → A
    exp x n = expR x n

  module BasicInstances (ℝ@(R , str) : CommRing ℓ) where

    open CommRingStr str 
    open GeneralUtils
    A = Polynomials {ℓ} {ℝ} 0 
    A^ : (n : ℕ) → CommAlgebra ℝ ℓ
    A^ n = pointwiseAlgebra (LFin n) A
    A[ξ] = Polynomials {ℓ} {ℝ} 1
    R[ξ] = CommAlgebra→CommRing A[ξ] 
    Poly : (n : ℕ) → CommAlgebra ℝ ℓ
    Poly = λ n → Polynomials {ℓ} {ℝ} n
    PolyAsRing : (n : ℕ) → CommRing ℓ
    PolyAsRing = λ n → CommAlgebra→CommRing (Poly n) 

  module FreeCommAlgebraUtils (ℝ@(R , strR) : CommRing ℓ) {n : ℕ} where

    open BasicInstances ℝ
    open AlgebraUtils ℝ (Poly n)
    open Construction ℝ 

    ξ : Fin n → ⟨ Poly n ⟩
    ξ i = var i
    expξ : Fin n → ℕ → fst (Poly n)
    expξ i k = exp (ξ i) k
    exp-var-vec : FinVec ℕ n →  FinVec ⟨ Poly n ⟩ n
    exp-var-vec r = λ i → expξ i (r i)
    constant : R → ⟨ Poly n ⟩
    constant a = const a
    monomial : R → Fin n → ℕ → ⟨ Poly n ⟩
    monomial a i n = (constant a) · (expξ i n)

  module 1DFreeCommAlgebraUtils (ℝ@(R , strR) : CommRing ℓ) where

    open BasicInstances ℝ
    open FreeCommAlgebraUtils ℝ
    open AlgebraUtils ℝ
    gen : (m : ℕ) → ⟨ A[ξ] ⟩
    gen m = expξ zero m
    var-power : ℕ → FinVec ⟨ A[ξ] ⟩ 1
    var-power n = λ x → gen (suc n)
    p0 : ⟨ Polynomials {ℓ} {ℝ} 1 ⟩
    p0 = expξ zero 0
    evPolyChar0 : (A : CommAlgebra ℝ ℓ) → (v : FinVec ⟨ A ⟩ 1) → evPoly A p0 v ≡ CommAlgebraStr.1a (snd A)
    evPolyChar0 A v = evPoly A p0 v ≡⟨ cong (λ P → evPoly A P v) helper ⟩ 
                      evPoly {ℓ} {ℝ} {1} A (Construction.1a ℝ) v ≡⟨ CommAlgebraStr.⋆-lid (snd A) (CommAlgebraStr.1a (snd A)) ⟩ 
                      CommAlgebraStr.1a (snd A) ∎
      where
        helper : expξ {1} zero 0 ≡ Construction.1a ℝ
        helper = refl
    evPolyChar : (A : CommAlgebra ℝ ℓ) → (n : ℕ) → (v : FinVec ⟨ A ⟩ 1) → evPoly A (gen n) v ≡ exp A (v zero) n
    evPolyChar A zero = evPolyChar0 A
    evPolyChar A (suc n) v = evPoly A (gen (suc n)) v                                                       ≡⟨ cong (λ P → evPoly A P v) helper1 ⟩ 
                             evPoly A ((ξ zero) Construction.· (gen n)) v                                   ≡⟨ IsAlgebraHom.pres· (snd (freeInducedHom A v)) (ξ zero) (gen n) ⟩ 
                             ((snd A) CommAlgebraStr.· evPoly A ( ξ {1} zero) v) (evPoly A (gen n) v)       ≡⟨ refl ⟩ 
                             ((snd A) CommAlgebraStr.· (v zero)) (evPoly A (gen n) v)                       ≡⟨ cong (λ a → ((snd A) CommAlgebraStr.· (v zero)) a) (evPolyChar A n v) ⟩ 
                             exp A (v zero) (suc n) ∎
      where
        helper1 : expξ {1} zero (suc n) ≡ ((ξ zero) Construction.· (gen n))
        helper1 = refl

    open Construction ℝ
    d/dξ : ⟨ A[ξ] ⟩ → ⟨ A[ξ] ⟩
    d/dξ (const c) = 0a
    d/dξ (var i) = 1a
    d/dξ (p + q) = (d/dξ p) + (d/dξ q)
    d/dξ (- p) = - (d/dξ p)
    d/dξ (p · q) = ((d/dξ p) · q) + (p · (d/dξ q))
    d/dξ (+-assoc p q r i) = +-assoc (d/dξ p) ((d/dξ q)) ((d/dξ r)) i
    d/dξ (+-rid p i) = +-rid (d/dξ p) i
    d/dξ (+-rinv p i) = +-rinv (d/dξ p) i
    d/dξ (+-comm p q i) = +-comm (d/dξ p) (d/dξ q) i
    d/dξ (·-assoc p q r i) = (((d/dξ p · (q · r)) + (p · ((d/dξ q · r) + (q · d/dξ r)))) ≡⟨ cong (λ a → a + (p · ((d/dξ q · r) + (q · d/dξ r)))) (·-assoc (d/dξ p) q r) ⟩ 
                              (((d/dξ p · q ) · r) + (p · ((d/dξ q · r) + (q · d/dξ r)))) ≡⟨ cong (λ a → ((d/dξ p · q ) · r) + a) (·-comm p ((d/dξ q · r) + (q · d/dξ r))) ⟩ 
                              (((d/dξ p · q ) · r) + (((d/dξ q · r) + (q · d/dξ r)) · p)) ≡⟨ cong (λ a → ((d/dξ p · q ) · r) + a) (ldist (d/dξ q · r) (q · d/dξ r) p) ⟩ 
                              (((d/dξ p · q ) · r) + (((d/dξ q · r) · p) + ((q · d/dξ r) · p))) ≡⟨ +-assoc ((d/dξ p · q) · r) ((d/dξ q · r) · p) ((q · d/dξ r) · p) ⟩ 
                              ((((d/dξ p · q ) · r) + ((d/dξ q · r) · p)) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + a) + ((q · d/dξ r) · p)) (sym (·-assoc (d/dξ q) r p)) ⟩ 
                              ((((d/dξ p · q ) · r) + (d/dξ q · (r · p))) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + (d/dξ q · a)) + ((q · d/dξ r) · p)) (·-comm r p) ⟩ 
                              ((((d/dξ p · q ) · r) + (d/dξ q · (p · r))) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) · r) + a) + ((q · d/dξ r) · p)) (·-assoc (d/dξ q) p r) ⟩
                              ((((d/dξ p · q ) · r) + ((d/dξ q · p) · r)) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → a + ((q · d/dξ r) · p)) (sym (ldist (d/dξ p · q) (d/dξ q · p) r)) ⟩ 
                              ((((d/dξ p · q ) + (d/dξ q · p)) · r) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) + a) · r) + ((q · d/dξ r) · p)) (·-comm (d/dξ q) p) ⟩ 
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + ((q · d/dξ r) · p)) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + a) (sym (·-assoc q (d/dξ r) p)) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · (d/dξ r · p))) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · a)) (·-comm (d/dξ r) p) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + (q · (p · d/dξ r))) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + a) (·-assoc q p (d/dξ r)) ⟩
                              ((((d/dξ p · q ) + (p · d/dξ q)) · r) + ((q · p) · d/dξ r)) ≡⟨ cong (λ a → (((d/dξ p · q ) + (p · d/dξ q)) · r) + (a · d/dξ r)) (·-comm q p) ⟩
                              ((((d/dξ p · q) + (p · d/dξ q)) · r) + ((p · q) · d/dξ r)) ∎) i
    d/dξ (·-lid p i) = (((0a · p) + (1a · d/dξ p)) ≡⟨ cong (λ a → a + (1a · (d/dξ p))) (RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) p) ⟩ 
                        (0a + (1a · d/dξ p)) ≡⟨ (+-comm 0a (1a · d/dξ p)) ∙ (+-rid (1a · d/dξ p)) ⟩ 
                        (1a · d/dξ p) ≡⟨ ·-lid (d/dξ p) ⟩ 
                        d/dξ p ∎) i
    d/dξ (·-comm p q i) = ((d/dξ p · q) + (p · d/dξ q) ≡⟨ +-comm (d/dξ p · q) (p · d/dξ q) ⟩ 
                           (p · d/dξ q) + (d/dξ p · q) ≡⟨ cong (λ a → a + (d/dξ p · q)) (·-comm p (d/dξ q)) ⟩ 
                           (d/dξ q · p) + (d/dξ p · q) ≡⟨ cong (λ a → (d/dξ q · p) + a) (·-comm (d/dξ p) q) ⟩ 
                           (d/dξ q · p) + (q · d/dξ p) ∎) i
    d/dξ (ldist p q r i) = ((((d/dξ p + d/dξ q) · r) + ((p + q) · d/dξ r)) ≡⟨ cong (λ a → a + ((p + q) · d/dξ r)) (ldist (d/dξ p) (d/dξ q) r) ⟩ 
                            (((d/dξ p · r) + (d/dξ q · r)) + ((p + q) · d/dξ r)) ≡⟨ cong (λ a → ((d/dξ p · r) + (d/dξ q · r)) + a) (ldist p q (d/dξ r)) ⟩ 
                            (((d/dξ p · r) + (d/dξ q · r)) + ((p · d/dξ r) + (q · d/dξ r))) ≡⟨ +-assoc ((d/dξ p · r) + (d/dξ q · r)) (p · d/dξ r) (q · d/dξ r) ⟩ 
                            ((((d/dξ p · r) + (d/dξ q · r)) + (p · d/dξ r)) + (q · d/dξ r)) ≡⟨ cong (λ a → a + (q · d/dξ r)) (sym (+-assoc (d/dξ p · r) (d/dξ q · r) (p · d/dξ r))) ⟩ 
                            (((d/dξ p · r) + ((d/dξ q · r) + (p · d/dξ r))) + (q · d/dξ r)) ≡⟨ cong (λ a → ((d/dξ p · r) + a) + (q · d/dξ r)) (+-comm (d/dξ q · r) (p · d/dξ r)) ⟩ 
                            (((d/dξ p · r) + ((p · d/dξ r) + (d/dξ q · r))) + (q · d/dξ r)) ≡⟨ cong (λ a → a + (q · d/dξ r)) (+-assoc (d/dξ p · r) (p · d/dξ r) (d/dξ q · r)) ⟩ 
                            ((((d/dξ p · r) + (p · d/dξ r)) + (d/dξ q · r)) + (q · d/dξ r)) ≡⟨ sym (+-assoc ((d/dξ p · r) + (p · d/dξ r)) (d/dξ q · r) (q · d/dξ r)) ⟩ 
                            (((d/dξ p · r) + (p · d/dξ r)) + ((d/dξ q · r) + (q · d/dξ r))) ∎) i
    d/dξ (+HomConst s t i) = sym (+-rid 0a) i
    d/dξ (·HomConst s t i) = (0a ≡⟨ sym (+-rid 0a) ⟩ 
                              (0a + 0a) ≡⟨ cong (λ a → 0a + a) step1 ⟩ 
                              (0a + ((const s) · 0a)) ≡⟨ cong (λ a → a + ((const s) · 0a)) step2 ⟩ 
                              ((0a · (const t)) + ((const s) · 0a)) ∎) i
      where
        step1 : 0a ≡ (const s · 0a)
        step1 = sym (RingTheory.0RightAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) (const s))
        step2 : 0a ≡ 0a · (const t)
        step2 = sym (RingTheory.0LeftAnnihilates (CommRing→Ring (CommAlgebra→CommRing A[ξ])) (const t))
    d/dξ (0-trunc p q α β i j) = isSetCommAlgebra A[ξ] (d/dξ p) (d/dξ q) (cong d/dξ α) (cong d/dξ β) i j

    derivPowerRule : (n : ℕ)(P : ⟨ A[ξ] ⟩) → d/dξ (exp A[ξ] P (suc n)) ≡ (embedℕinAlg A[ξ] (suc n)) · ((exp A[ξ] P n) · (d/dξ P))
    derivPowerRule zero P = d/dξ (exp A[ξ] P 1) ≡⟨ cong (λ a → d/dξ a) help1 ⟩ 
                  d/dξ P ≡⟨ sym (·-lid (d/dξ P)) ⟩ 
                  (exp A[ξ] P zero · d/dξ P) ≡⟨ sym (·-lid (exp A[ξ] P zero · d/dξ P)) ⟩
                  (1a ·  (exp A[ξ] P zero · d/dξ P)) ≡⟨ cong (λ a → a · (exp A[ξ] P zero · d/dξ P)) help2 ⟩
                  (embedℕinAlg A[ξ] 1 · (exp A[ξ] P zero · d/dξ P)) ∎
      where
        help1 : (P · 1a) ≡ P
        help1 = (·-comm P 1a) ∙ (·-lid P)
        help2 : 1a ≡ 0a + 1a
        help2 = sym ((+-comm 0a 1a) ∙ (+-rid 1a))
    derivPowerRule (suc n) P = d/dξ (expo P (suc (suc n))) ≡⟨ refl ⟩   
                     d/dξ (P · expo P (suc n)) ≡⟨ refl ⟩  
                     ((d/dξ P · expo P (suc n)) + (P · d/dξ (expo P (suc n)))) ≡⟨ cong (λ a → (d/dξ P · expo P (suc n)) + (P · a)) (derivPowerRule n P) ⟩  
                     ((d/dξ P · expo P (suc n)) + (P · (n+1 · ((expo P n) · (d/dξ P))))) ≡⟨ cong (λ a → a + ((P · (n+1 · P^nP')))) (·-comm (d/dξ P) (expo P (suc n))) ⟩  
                     (P^snP' + (P · (n+1 · P^nP'))) ≡⟨ cong (λ a → P^snP' + a) ((·-assoc P n+1 P^nP') ∙ 
                                                                                (cong (λ a → a · P^nP') (·-comm P n+1)) ∙ 
                                                                                sym (·-assoc n+1 P P^nP')) ⟩
                     (P^snP' + (n+1 · (P · ((expo P n) · (d/dξ P))))) ≡⟨ cong (λ a → P^snP' + (n+1 · a))  (·-assoc P (expo P n) (d/dξ P)) ⟩  
                     (P^snP' + (n+1 · ((P · (expo P n)) · (d/dξ P)))) ≡⟨ cong (λ a → P^snP' + (n+1 · (a · (d/dξ P)))) refl ⟩
                     (P^snP' + (n+1 · P^snP')) ≡⟨ cong (λ a → a + (n+1 · P^snP')) (sym (·-lid P^snP')) ⟩
                     ((1a · P^snP') + (n+1 · P^snP')) ≡⟨ sym (ldist 1a n+1 P^snP') ⟩  
                     ((1a + n+1) · P^snP') ≡⟨ cong (λ a → a · P^snP') help1 ⟩
                     (n+2 · P^snP') ∎
      where
        n+1 = embedℕinAlg A[ξ] (suc n)
        n+2 = embedℕinAlg A[ξ] (suc (suc n))
        expo = exp A[ξ]
        P^nP' = expo P n · d/dξ P
        P^snP' = expo P (suc n) · d/dξ P
        help1 : (1a + n+1) ≡ (n+1 + 1a) -- ≡ n+2
        help1 = +-comm 1a n+1
    
    derivPowerRuleVar : (n : ℕ) → d/dξ (var-power n zero) ≡ (embedℕinAlg A[ξ] (suc n)) · ((exp A[ξ] (ξ zero) n) · (d/dξ (ξ zero)))
    derivPowerRuleVar n = derivPowerRule n (ξ zero)