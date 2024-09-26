{-# OPTIONS --cubical --safe #-}

module SDG.DifferentialCohesion.ISM.Base where

  open import Cubical.Foundations.Everything
  open import Cubical.Data.Nat
  open import Cubical.Data.FinData
  open import Cubical.Algebra.CommRing
  open import Cubical.Algebra.CommAlgebra
  open import Cubical.Algebra.CommAlgebra.FPAlgebra
  open import Cubical.Modalities.Modality
  open import Cubical.Foundations.Equiv.PathSplit
  
  open import Cubical.HITs.Nullification renaming (elim to elim-Null ; rec to Nrec)


  open import SDG.Base
  open import SDG.Infinitesimals.Instances
  open import SDG.WeilAlgebra.Instances
  open import SDG.Infinitesimals.Base
  
  module ModalConnected (mod : Modality ℓ) where

    open Modality mod

    ◯-isConnType : (A : Type ℓ) → Type ℓ
    ◯-isConnType A = isContr (◯ A)
    ◯-isConnMap : {A B : Type ℓ}(f : A → B) → Type ℓ
    ◯-isConnMap {B = B} f = (y : B) → ◯-isConnType (fiber f y)


  module NullProperties (X : Type ℓ) where

    private
      ∗ = Unit* {ℓ}

    mod = NullModality X
    open Modality mod public
    open ModalConnected mod public

    ◯A≃X→◯A : {A : Type ℓ} → Iso (◯ A) (X → ◯ A)
    ◯A≃X→◯A {A} = toIso (const {A = ◯ A} {B = X}) ◯-isModal
    constMapsEquivIso : (A : ◯-Types) → Iso (fst A) (X → (fst A))
    constMapsEquivIso A = toIso (const {A = fst A} {B = X}) (snd A)
    ◯X≃X→◯X : Iso (◯ X) (X → ◯ X)
    ◯X≃X→◯X = ◯A≃X→◯A {X}

    -- Properties of ∗
    ∗-isModal : isModal ∗
    ∗-isModal = record { sec = (λ _ → tt*) , λ b i x → tt* ; 
                         secCong = λ x y → (λ z i → tt*) , λ b i i₁ x₁ → tt* }
    ∗-iso-ℑ∗ : Iso ∗ (◯ ∗)
    ∗-iso-ℑ∗ = isModalToIso ∗-isModal


    -- the image of every map (S → Null S A) is contractible in Null S A,
    -- so the image of every map (Dsk → ℑ A) is contractible in ℑ A,
    -- so the image of η-Dsk : Dsk → ℑ Dsk  is contractible in ℑ Dsk,
    -- so ∀ (x y : ℑ Dsk) η (x) ≡ η (y).
    imageFromNullifierContr : {A : Type ℓ} → (f : X → ◯ A) → (x y : X) → f x ≡ f y 
    imageFromNullifierContr f x y i = ((sym (spoke f x)) ∙ spoke f y) i
    ηContrImg : (x y : X) → η x ≡ η y 
    ηContrImg x y i = imageFromNullifierContr η x y i
    -- Higher version of the previous implementation
    imageFromNullifierContr≡ : {x y : ◯ X} → (p : X → x ≡ y) → (s r : X) → p s ≡ p r
    imageFromNullifierContr≡ p s r = sym (≡spoke p s) ∙ (≡spoke p r)
    ηPath : (x y s : X) → η x ≡ η y 
    ηPath = λ x y s i → ηContrImg x y i
    ηContrImg≡ : {x y : X} → (p : X → η x ≡ η y) → (s r : X) 
                              → ηPath x y s ≡ ηPath x y r
    ηContrImg≡ {x = x} {y = y} p s r = imageFromNullifierContr≡ (λ x₁ i → ηContrImg x y i) s r
    -- 

    sectOfPrecomp→isModalConn : {A B : Type ℓ}{f : A → B} → ((P : B → ◯-Types)
                                → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f))
                                →  ◯-isConnMap f
    sectOfPrecomp→isModalConn {A} {B} {f} P→sect b = (c P→sect b) , λ y → sym (fun P→sect b y)
        where            
            c : ((P : B → ◯-Types)
                → hasSection (λ(s : (b : B) → P b .fst) → s ∘ f)) → (b : B)
                → ◯ (fiber f b)
            c s = fst (s λ b → (◯ (fiber f b) , Modality.◯-isModal mod)) λ a → η (a , refl)
            fun : (P→sect : ((P : B → ◯-Types)
                    → hasSection λ(s : (b : B) → P b .fst) → s ∘ f))
                    → (b : B) (w : (◯ (fiber f b)))
                    → w ≡ c P→sect b
            fun P→sect b = Modality.◯-elim mod (λ x → Modality.◯-=-isModal mod _ _) 
                            λ a → J (λ b p → (η ((fst a) , p)) ≡ c P→sect b) (c* (fst a)) (snd a)
                where
                c* : ((a : A) → η (a , refl {x = f a})  ≡ c P→sect (f a))
                c* a = sym (cong (λ x → x a) (P→sect (λ b → ◯ (fiber f b) , Modality.◯-isModal mod) .snd λ a → η (a , refl)))
    
    ◯-connectedTruncIso :  {A B : Type ℓ}{f : A → B} → ◯-isConnMap f
                             → Iso (◯ A) (◯ B)
    ◯-connectedTruncIso {A} {B} {f} con = g
      where
        back : B → ◯ A
        back y = ◯-map fst (con y .fst)
        backSection : (b : B) → Path  (◯ B) 
                                      (◯-rec 
                                        ◯-isModal 
                                        (λ x → η (f x)) 
                                        (◯-rec ◯-isModal back (η b))) 
                                      (η b)
        backSection b = helper (λ p → ◯-map f p ≡ η b) 
                                (λ x → Modality.◯-=-isModal mod _ _) 
                                (λ a p → cong ∣_∣ p) 
                                (fst (con b))
          where
            helper :   {C : A → Type ℓ}(P : ◯ A → Type ℓ)
                        → ((x : ◯ (Σ A C)) → Modality.isModal mod (P (◯-map fst x)))
                        → ((a : A) (b : C a) → P (η a))
                        → (p : ◯ (Σ A C))
                        →  P (◯-map fst p)
            helper P mod' pf = Modality.◯-elim mod mod' λ x → pf (fst x) (snd x)
        g : Iso (◯ A) (◯ B)
        Iso.fun g = ◯-map f
        Iso.inv g = Modality.◯-rec mod ◯-isModal back
        Iso.leftInv g = Modality.◯-elim mod
                                         (λ x → ◯-=-isModal _ _) 
                                         λ a → cong (◯-map fst) ((con (f a) .snd (η (a , refl))))  -- With a generic modality the ◯-map fst gets stuck
        Iso.rightInv g = Modality.◯-elim mod 
                                          (λ x → ◯-=-isModal _ _)
                                          backSection

    
    constMapsIso : (A : ◯-Types) → Iso (∗  → (fst A)) (fst A)
    constMapsIso A =  iso (λ x → x tt*) (λ x x₁ → x) (λ b i → b) λ a i x → a tt*
    nullifierActsAsUnitIso :  (A : ◯-Types) → Iso (∗ → (fst A)) (X → (fst A))
    nullifierActsAsUnitIso A = compIso (constMapsIso A) (constMapsEquivIso A)
    constMapsIsEquiv :  (A : ◯-Types) → isEquiv (λ x _ → x tt*)
    constMapsIsEquiv A = isoToIsEquiv (nullifierActsAsUnitIso A)
    modalTypesHaveSect : (A : ∗ → ◯-Types) → hasSection (λ x _ → x tt*)
    modalTypesHaveSect A = isEquiv→hasSection (constMapsIsEquiv (A tt*))
    nullifierReflectsToUnitIso : Iso (◯ X) ∗
    nullifierReflectsToUnitIso = compIso (◯-connectedTruncIso (sectOfPrecomp→isModalConn modalTypesHaveSect)) 
                  (invIso (∗-iso-ℑ∗))  
    
    nullifierReflectsToUnitIsoPath : (◯ X) ≡ ∗
    nullifierReflectsToUnitIsoPath = isoToPath (nullifierReflectsToUnitIso)
    isContModalType : isContr (◯ X)
    isContModalType = (Iso.fun (invIso nullifierReflectsToUnitIso) tt*) , Iso.leftInv nullifierReflectsToUnitIso
    -- property1 : (A B : Type ℓ) (f : A → B)(y : B) → ◯ (fiber f y) → isContr (◯ A) → isContr (◯ (fiber f y))
    -- property1 A B f y p isContr◯A = p , λ z → {!   !}


    RetrNullifierReflectsToUnitIso : {A : Type ℓ}
      (f : A → X) (g : X → A)
      (h : (x : A) → g (f x) ≡ x)
       → Iso {ℓ} {ℓ} (◯ A) ∗
    RetrNullifierReflectsToUnitIso {A} f g h = iso (λ _ → tt*) 
                         (λ x → fst (retrImplyIsConn f g h)) 
                         (λ b i → tt*) 
                         λ a i → (snd (retrImplyIsConn f g h)) a i
      where
        isModalConnType : ◯-isConnType X
        isModalConnType = isContModalType
        ℑ-isConnectedRetract : {A : Type ℓ} {B : Type ℓ}
          (f : A → B) (g : B → A)
          (h : (x : A) → g (f x) ≡ x)
          → ◯-isConnType B → ◯-isConnType A
        ℑ-isConnectedRetract f g h = isContrRetract 
                                      (◯-map f) 
                                      (◯-map g) 
                                      (◯-elim 
                                        (λ _ → ◯-=-isModal _ _) 
                                        λ x → cong η (h x))
        retrImplyIsConn : {A : Type ℓ}
          (f : A → X) (g : X → A)
          (h : (x : A) → g (f x) ≡ x)
          → ◯-isConnType A
        retrImplyIsConn f g h = ℑ-isConnectedRetract f g h isModalConnType
      
  module Monad (ℝ@(R , str) : CommRing ℓ) where

    open 1Disk ℝ
    open BasicInstances ℝ
    ISM : Modality ℓ
    ISM = NullModality (infDskOfOrder∞ A)
    ℑ = Modality.◯ ISM
    η = Modality.η ISM
    ℑ-rec = Modality.◯-rec ISM
    ℑ-Type = Modality.◯-Types ISM  