{-# OPTIONS --cubical --safe #-}

module SDG.DifferentialCohesion.ISM.Properties where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.Nat
  open import Cubical.Data.FinData
  open import Cubical.Data.Sigma
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Modalities.Modality
  open import Cubical.Foundations.Equiv.PathSplit
  
  open import Cubical.HITs.Localization renaming (rec to Lrec)
  open import Cubical.HITs.Nullification renaming (elim to elim-Null ; rec to Nrec)
  open import Cubical.Data.Unit
  open import Cubical.Data.Empty
  open import Cubical.Functions.Embedding

  open import Cubical.HITs.PropositionalTruncation renaming (elim to elim-Prop ; rec to Prec)

  open import Cubical.Relation.Nullary
  open import Cubical.Algebra.CommRingSolver.Utility

  open import SDG.Base
  open import SDG.Infinitesimals.Instances
  open import SDG.WeilAlgebra.Instances
  open import SDG.Infinitesimals.Base
  open import SDG.DifferentialCohesion.ISM.Base

  module BasicProperties (ℝ@(R , str) : CommRing ℓ) where

    open 1Disk ℝ
    open BasicInstances ℝ
    open RingUtils (CommAlgebra→CommRing A)
    open 1DFreeCommAlgebraUtils ℝ
    open NullProperties (infDskOfOrder∞ A)
    open CommRingStr (snd (CommAlgebra→CommRing A))
    private
      D = infDskOfOrder∞ A
      ι : D → ⟨ A ⟩
      ι d = fromZeroLocus₁ 1 (var-power (fst d)) A (snd d) zero
      _at_ = polynomialAt
      infDispl : {n : ℕ} → FinVec ⟨ CommAlgebra→CommRing A ⟩ n → D → ⟨ CommAlgebra→CommRing A ⟩
      infDispl p d = p at ι d
      0D : D
      0D = (1 , (0d A 1))
      
    infDisplIsNullified : (n : ℕ)(p q : FinVec ⟨ CommAlgebra→CommRing A ⟩ n) (a b : D) → η (p at ι 0D) ≡ η (q at ι 0D) →
                          η (infDispl p a) ≡ η (infDispl q b) 
    infDisplIsNullified n p q a b sC = (ηinfDispl≡ηEvalAt0 p a ∙ sC ∙ sym (ηinfDispl≡ηEvalAt0 q a)) ∙ ηinfDisplConnImg q a b
      where
        ηinfDisplConnImg : (p : FinVec ⟨ CommAlgebra→CommRing A ⟩ n) → (a b : D) → η (infDispl p a) ≡ η (infDispl p b)
        ηinfDisplConnImg p a b = precompByηContrImg (infDispl p) a b
          where
            precompByηContrImg : {X : Type ℓ}(f : D → X) (x y : D) → η (f x) ≡ η (f y)
            precompByηContrImg f x y = imageFromNullifierContr (η ∘ f) x y
        ηinfDispl≡ηEvalAt0 : (p : FinVec ⟨ CommAlgebra→CommRing A ⟩ n)(a : D) → η (infDispl p a) ≡ η (p at ι 0D)
        ηinfDispl≡ηEvalAt0 p a =  (ηinfDisplConnImg p a 0D) ∙ cong η refl

  module KillInfinitesimalDisk (ℝ@(R , str) : CommRing ℓ) where
    
    open BasicInstances ℝ
    open 1Disk ℝ -- n-disk → ∞-disk
    open 1DFundamentalWeilAlgebras ℝ
    open 1DFreeCommAlgebraUtils ℝ
    open NullProperties (infDskOfOrder∞ A) -- Nullification at the ∞-disk
    open AlgebraSpectrum ℝ
    private
      ∗ = Unit*

    -- Final Theorem 1 :: Nullification at infDiskOfOrder∞ nullifies all infDsisksOfOrder n
    ℑKillDisksOfAnyOrder : (n : ℕ) → Iso {ℓ} {ℓ} (◯ (infDskOfOrder A n)) ∗
    ℑKillDisksOfAnyOrder n = RetrNullifierReflectsToUnitIso (incl A n) (retr A n) (isRetrRetr n A)    

    ℑKillDisksOfAnyOrderMaps : (n : ℕ)(X : Type ℓ)  → Iso {ℓ} {ℓ} (◯ (infDskOfOrder A n) → X) (∗ → X)
    Iso.fun (ℑKillDisksOfAnyOrderMaps n X) = λ x x₁ → x (Iso.inv (ℑKillDisksOfAnyOrder n) tt*)
    Iso.inv (ℑKillDisksOfAnyOrderMaps n X) = λ x x₁ → x (Iso.fun (ℑKillDisksOfAnyOrder n) (η (0d A n)))
    Iso.rightInv (ℑKillDisksOfAnyOrderMaps n X) = λ b → funExt (λ x → cong (λ z → b z) (Iso.rightInv (ℑKillDisksOfAnyOrder n) x))
    Iso.leftInv (ℑKillDisksOfAnyOrderMaps n X) = λ a → funExt (λ x → cong (λ z → a z) (Iso.leftInv (ℑKillDisksOfAnyOrder n) x))

    -- Final Theorem 2 :: ℑ Kills Fundamental FPNAs Specs
    ℑKill1DFundFPNAs : (n : ℕ) → Iso (◯ (Spec (W n))) ∗
    ℑKill1DFundFPNAs n = compIso (ℑhelperIso n) (ℑKillDisksOfAnyOrder n)
      where
        -- Helper Lemma :: ℑ preserves FPHomIso, via equivalences
        ℑhelperIso : (n : ℕ) → Iso (◯ (Spec (W n)))  (◯ (infDskOfOrder A n))
        ℑhelperIso n = equivToIso (◯-map (fst (isoToEquiv (FPHomIso 1 (var-power n)))) , 
                                        (◯-preservesEquiv (fst (isoToEquiv (FPHomIso 1 (var-power n)))) 
                                                            (snd (isoToEquiv (FPHomIso 1 (var-power n))))))

 
  module KillInfinitesimalDiskSet (ℝ@(R , str) : CommRing ℓ) where
    open BasicInstances ℝ
    open 1Disk ℝ -- n-disk → ∞-disk
    open 1DFundamentalWeilAlgebras ℝ
    open 1DFreeCommAlgebraUtils ℝ
    open NullProperties (infDskOfOrder∞ A) -- Nullification at the ∞-disk
    open AlgebraSpectrum ℝ
    open KillInfinitesimalDisk ℝ
    private
      ∗ = Unit* {ℓ}
      D' : Type ℓ
      D' = infDskOfOrder∞ A
      D = Σ[ d ∈ FinVec (typ A) 1 ] ∥ Σ[ k ∈ ℕ ] ((i : Fin 1) → evPoly A (var-power k i) d ≡ CommAlgebraStr.0a (snd A))  ∥₁
      D'' = Σ[ d ∈ FinVec (typ A) 1 ] Σ[ k ∈ ℕ ] ((i : Fin 1) → evPoly A (var-power k i) d ≡ CommAlgebraStr.0a (snd A))  
      0D' : D'
      0D' = (1 , (0d A 1))
      D[_] = infDskOfOrder A
      
    e : D' → D
    e (k , (x , p)) = x , ∣ k , p ∣₁

    e2 : D'' → D
    e2 (x , (k , p)) = x , ∣ k , p ∣₁

    -- h2 : D → D''
    -- h2 (x , p) = x , {!   !} , {!   !}
    
    

    eHasMerePreimage : (y : D) → ∥ Σ[ x ∈ D' ] e x ≡ y ∥₁
    eHasMerePreimage y = Prec isPropPropTrunc 
                              (λ x → ∣ ((fst x) , fst y , λ i → snd x zero) , Σ≡Prop (λ z → isPropPropTrunc) refl ∣₁) 
                              (snd y)
    


    isSetD' : isSet D'
    isSetD' = isSetΣ isSetℕ (λ k → isSetZeroLocus 1 (var-power k) A)

    isSetD : isSet D
    isSetD = isSetΣ (isSet→ (isSetCommAlgebra A)) λ x → isProp→isSet isPropPropTrunc

    0D = e 0D'

    -- fibElem : (y : D) → ∥ fiber e y ∥₁ → D'
    -- fibElem y d = {!   !}
    -- h : D → D'
    -- h y = fibElem y {!   !} --(Prec {!   !} (λ x → x) (eHasMerePreimage y))

    incl2 : (n : ℕ) → D[ n ] → D
    incl2 n d = e (incl A n d)

    -- N : (n : ℕ)(X : ◯-Types)(g : D[ n ] → ⟨ X ⟩)(x : D[ n ]) → g x ≡ g (0d A n)
    -- N n X g x = 
    
    exp1 : (n : ℕ) → (Σ[ d ∈ FinVec ⟨ A ⟩ 1 ] ∥ ((i : Fin 1) → (evPoly A (var-power n i) d) ≡ CommAlgebraStr.0a (snd A)) ∥₁) → D[ n ]
    exp1 n p = (fst p) , λ i → Prec (isSetCommAlgebra A (evPoly A (var-power n i) (fst p)) (CommAlgebraStr.0a (snd A))) (λ H → H i) (snd p) --(Prec (isProp→ ?) {!   !} (snd p))
    -- exp2 : (n : ℕ) → D → (Σ[ d ∈ FinVec ⟨ A ⟩ 1 ] ∥ ((i : Fin 1) → (evPoly A (var-power n i) d) ≡ CommAlgebraStr.0a (snd A)) ∥₁)
    -- exp2 n d = (fst d) , (Prec isPropPropTrunc help (snd d))
    --   where
    --     help : Σ[ k ∈ ℕ ] ((i : Fin 1) → evPoly A (var-power k i) (fst d) ≡ CommAlgebraStr.0a (snd A)) → ∥ ((i : Fin 1) → evPoly A (var-power n i) (fst d) ≡ CommAlgebraStr.0a (snd A)) ∥₁
    --     help z with discreteℕ (fst z) k= {!   !}
    
    --retr2 : (n : ℕ) → D → D[ n ]
    --retr2 n (m , d) = {!   !}

    -- DIso : (X : ◯-Types) → Iso (D → ⟨ X ⟩) (∗ → ⟨ X ⟩)
    -- Iso.fun (DIso X) = λ f _ → f 0D
    -- Iso.inv (DIso X) = λ c _ → c tt*
    -- Iso.rightInv (DIso X) = λ g → refl
    -- Iso.leftInv (DIso X) = λ f → funExt (λ x → {! Iso.inv (DIso X isSetX) (Iso.fun (DIso X isSetX) f) x !} ≡⟨ {!   !} ⟩ 
    --                                                   {!   !} ≡⟨ {!   !} ⟩
    --                                                   {!   !} ≡⟨ {!   !} ⟩
    --                                                   {!   !} ≡⟨ {!   !} ⟩
    --                                                   {!   !} ≡⟨ {!   !} ⟩
    --                                                   {!   !} ≡⟨ {!   !} ⟩
    --                                                   {!   !} ∎)


    -- newincl : (y : D) → D' → fiber e y
    -- newincl y p = rec→Set (isSetΣ isSetD' λ x → isProp→isSet (isSetD (e x) y)) (λ q → {!   !}) (λ a b → {!   !}) (eHasMerePreimage y)
    --   where
    --     help1 : (y : D) → D' → fiber e y → fiber e y
    --     help1 y (n , p) ((k , q) , inFib) with discreteℕ n k
    --     ... | yes p = {!   !}
    --     ... | no ¬p = {!   !}
    -- ePrecHasSection :  (y : D) → isContr (◯ (fiber e y))
    -- ePrecHasSection y = Prec isPropIsContr (λ x → {!   !}) (eHasMerePreimage y)
    --   where
    --     help1 : {!   !}
    --     help1 = {!   !}


-- Σ (◯ (infDskOfOrder∞ A))
--       (λ x₁ → (y₁ : ◯ (infDskOfOrder∞ A)) → x₁ ≡ y₁)

    -- ηe : ◯ D' → ◯ D
    -- ηe = ((λ _ → η (e 0D')) ∘ Iso.fun nullifierReflectsToUnitIso)

    -- u! : ◯ D → ◯ D'
    -- u! p = Iso.inv nullifierReflectsToUnitIso tt*

    -- -- DskIso : Iso (◯ D') (◯ D)
    -- -- Iso.fun DskIso = ηe
    -- -- Iso.inv DskIso = u!
    -- -- Iso.rightInv DskIso = λ b → (((λ _ → η (e 0D')) ∘ Iso.fun nullifierReflectsToUnitIso) ∘ Iso.inv nullifierReflectsToUnitIso) tt* ≡⟨ refl ⟩ 
    -- --                             η (e 0D') ≡⟨ {!   !} ⟩ 
    -- --                             {!   !} ≡⟨ {!   !} ⟩ 
    -- --                             b ∎
    -- -- Iso.leftInv DskIso = λ a → snd isContModalType a



    -- -- eInv : D → D'
    -- -- eInv (x , nilp) = {!   !} , (x , (Prec (isProp→ {!   !}) {!   !} nilp))

    -- h : (n : ℕ) → D[ n ] → D
    -- h n (x , p) = x , ∣ n , p ∣₁

    
    -- open import Cubical.Relation.Nullary
    -- open import Cubical.Algebra.CommRingSolver.Utility
    
    -- open import Cubical.Data.Bool
    -- open import Cubical.Data.Nat.Order

    -- -- hInv : (n : ℕ) → ((x , p) : D) → D[ rec→Set isSetℕ (λ z → n) (λ a b → refl) p ]
    -- -- hInv n (x , p) = {!   !}
    -- -- hInv : (n : ℕ) → D → D[ n ]
    -- -- hInv n d = (fst d) , (λ i → Prec (isSetCommAlgebra A (evPoly A (var-power n i) (fst d)) (CommAlgebraStr.0a (snd A))) 
    -- --                                  (λ x → help1 i x)
    -- --                                  (snd d))
    -- --   where
    -- --     help1 : (i : Fin 1)(x : Σ[ k ∈ ℕ ] ((j : Fin 1) → evPoly A (var-power k j) (fst d) ≡ CommAlgebraStr.0a (snd A))) → 
    -- --             evPoly A (var-power n i) (fst d) ≡ CommAlgebraStr.0a (snd A)
    -- --     help1 i x = (snd (retr A n ({!  !} , ((fst d) , (snd x))))) i
    --     -- ... | yes p = transport (λ j → evPoly A (var-power (p j) i) (fst d) ≡ CommAlgebraStr.0a (snd A)) (snd x i) --transport (λ i → zeroLocus {ℓ} {ℝ} {1} 1 (λ x → gen (suc (p i))) A) d
    --     -- ... | no ¬p = byAbsurdity (¬p {!   !}) --0d A n 
    -- -- lem2 : (y : D) → isSet (Σ[ x ∈ D' ] e x ≡ y)
    -- -- lem2 y = λ x z → {! lem1  !}
  

    -- eHasMerePreimage : (y : D) → ∥ Σ[ x ∈ D' ] e x ≡ y ∥₁
    -- eHasMerePreimage y = Prec isPropPropTrunc 
    --                           (λ x → ∣ ((fst x) , fst y , λ i → snd x) , Σ≡Prop (λ z → isPropPropTrunc) refl ∣₁) 
    --                           (snd y)
    
    
    -- isSetD' : isSet D'
    -- isSetD' = isSetΣ isSetℕ (λ k → isSetZeroLocus 1 (var-power k) A)

    -- isSetD : isSet D
    -- isSetD = isSetΣ (isSet→ (isSetCommAlgebra A)) λ x → isProp→isSet isPropPropTrunc
    
    -- eHasMerePreimage : (y : D) → Σ[ x ∈ D' ] e x ≡ y 
    -- eHasMerePreimage y = rec→Set {!   !} {!   !} {!   !} {!   !}  --rec→Set (isSetΣ isSetD' (λ x → isProp→isSet (isSetD (e x) y))) (λ z → {!   !} , Σ≡Prop (λ z → isPropPropTrunc) refl) (λ a b → {!   !}) (snd y)
  

    -- -- open import Cubical.Functions.Surjection
    -- -- eSurjection : isSurjection e
    -- -- eSurjection = eHasMerePreimage

    -- -- mapsFromDToModalTAreMerelyCosntant : (X : ◯-Types) (x : D) (f : D → ⟨ X ⟩) → f 0D ≡ f x
    -- -- mapsFromDToModalTAreMerelyCosntant X x f = {!   !}
    
    -- -- -- stuck when trying to prove things for arbitrary types that we don't know if they are sets, or higher groupoids.
    -- -- mapsFromDToModalTAreMerelyCosntant : (X : ◯-Types) (f : D → ⟨ X ⟩) → (x : D) → ∥ f 0D ≡ f x ∥₁
    -- -- mapsFromDToModalTAreMerelyCosntant X f x = Prec isPropPropTrunc 
    -- --                                           (λ z → ∣ sym (f x ≡⟨ cong f (sym (snd z)) ⟩ 
    -- --                                                    (f ∘ e) (fst z) ≡⟨ sym (step5 (f ∘ e) (fst z)) ⟩ 
    -- --                                                    (f ∘ e) 0D' ≡⟨ refl ⟩ 
    -- --                                                    f 0D ∎) ∣₁) 
    -- --                                           (eHasMerePreimage x)
    -- --   where 
    -- --     step1 : (g : D' → ◯ (⟨ X ⟩)) → (y : D') → g 0D' ≡ g y
    -- --     step1 g y = imageFromNullifierContr g 0D' y
    -- --     step3 :  (g : D' → ⟨ X ⟩) → (y : D') → (Iso.fun (isModalToIso (snd X))  ∘ g) 0D' ≡ (Iso.fun (isModalToIso (snd X))  ∘ g) y
    -- --     step3 g y = step1 (Iso.fun (isModalToIso (snd X))  ∘ g) y
    -- --     step4 :  (g : D' → ⟨ X ⟩) → (y : D') → (Iso.inv (isModalToIso (snd X)) ∘ Iso.fun (isModalToIso (snd X))  ∘ g) 0D' ≡ (Iso.inv (isModalToIso (snd X)) ∘ Iso.fun (isModalToIso (snd X))  ∘ g) y
    -- --     step4 g y = cong (Iso.inv (isModalToIso (snd X))) (step3 g y)
    -- --     step5 : (g : D' → ⟨ X ⟩) → (y : D') → g 0D' ≡ g y
    -- --     step5 g y = g 0D' ≡⟨ cong (λ a → a 0D') (sym (funExt λ z → Iso.leftInv (isModalToIso (snd X)) (g 0D'))) ⟩
    -- -- --                 (Iso.inv (isModalToIso (snd X)) ∘ Iso.fun (isModalToIso (snd X))  ∘ g) 0D' ≡⟨ step4 g y ⟩
    -- -- --                 (Iso.inv (isModalToIso (snd X)) ∘ Iso.fun (isModalToIso (snd X))  ∘ g) y ≡⟨ cong (λ a → a y) (funExt (λ z → Iso.leftInv (isModalToIso (snd X)) (g y))) ⟩
    -- -- --                 g y ∎
                    
    -- -- -- eInv : D → ∥ D' ∥₁
    -- -- -- eInv z = Prec isPropPropTrunc (λ x → ∣ fst x ∣₁) (eHasMerePreimage z)

    -- DIso : (X : ◯-Types)(isSetX : isSet ⟨ X ⟩) → Iso (D → ⟨ X ⟩) (∗ → ⟨ X ⟩)
    -- Iso.fun (DIso X isSetX) = λ f _ → f 0D
    -- Iso.inv (DIso X isSetX) = λ c _ → c tt*
    -- Iso.rightInv (DIso X isSetX) = λ b → refl
    -- Iso.leftInv (DIso X isSetX) = λ a → funExt (λ x → {!   !})


  


    -- -- constMapsIsEquivD :  (X : ◯-Types)(isSetX : isSet ⟨ X ⟩) → isEquiv (λ x _ → x tt*)
    -- -- constMapsIsEquivD X isSetX = isoToIsEquiv (invIso (DIso X isSetX))
    -- -- modalTypesHaveSectD : (X : ∗ → ◯-Types)(isSetX : isSet ⟨ X tt* ⟩)  → hasSection (λ x _ → x tt*)
    -- -- modalTypesHaveSectD X isSetX = isEquiv→hasSection (constMapsIsEquivD (X tt*) isSetX)

    -- -- nullifierReflectsToUnitIsoD : Iso (◯ D) ∗
    -- -- nullifierReflectsToUnitIsoD = compIso (◯-connectedTruncIso (sectOfPrecomp→isModalConn λ P → modalTypesHaveSectD P {!   !})) (invIso (∗-iso-ℑ∗))

  

    -- -- mapsFromDToModalTAreCosntant : (X : ◯-Types) (f : D → ⟨ X ⟩) (y : D) (z : Σ[ a ∈ D' ] e a ≡ y ) →  f 0D ≡ f y
    -- -- mapsFromDToModalTAreCosntant = {!   !}
    -- -- DActsAsUnitIso :  (A : ◯-Types) → Iso (∗ → (fst A)) (D → (fst A))
    -- -- DActsAsUnitIso A = compIso (constMapsIso A) (constDMapsEquivIso A) --compIso (constMapsIso A) (constDMapsEquivIso A)

    -- -- ePrecHasSection : (P : D → ◯-Types) → hasSection (λ(s : (b : D) → P b .fst) → s ∘ e)
    -- -- ePrecHasSection P = (λ x → {! x ∘ e  !}) , {!   !}

    -- -- ePrecHasSection :  (y : D) → isContr (◯ (fiber e y))
    -- -- ePrecHasSection y = Prec isPropIsContr (λ x → {!   !}) (eHasMerePreimage y)
    -- --   where
    -- --     inc : fiber e y → D'
    -- --     inc p = fst p
    -- --     ret : D' → fiber e y
    -- --     ret d = d , {!   !}
    --   -- where
    --   --   step1 :  {!   !}
    --   --   step1 d = {!   !}                  