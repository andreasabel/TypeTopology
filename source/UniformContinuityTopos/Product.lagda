---
title: Binary Product of Sheaves
author: Ayberk Tosun
---

\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.Miscelanea
open import UF.UA-FunExt
open import MLTT.Fin

open import UF.SIP-Examples
open monoid

module UniformContinuityTopos.Product
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Sheaf pt fe
open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.UniformContinuityCoverage pt fe
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt

\end{code}

The product of two sheaves

\begin{code}

_×ₛ_ : Sheaf 𝓤 → Sheaf 𝓥 → Sheaf (𝓤 ⊔ 𝓥)
_×ₛ_ {𝓤 = 𝓤} {𝓥} (𝒫@((P , σ₁) , (_·₁_ , _)) , ♠₁)  (𝒬@((Q , σ₂) , (_·₂_ , _)) , ♠₂) = ℛ , ♠
  where
   _∙×_ : (P × Q) → ⟪ ℂ ⟫ → P × Q
   ((p , q) ∙× t) = p ·₁ t , q ·₂ t

   γ : is-[ ℂ ]-action (×-is-set σ₁ σ₂) _∙×_ holds
   γ = (λ { (p , q) → γ₁ p q }) , γ₂
    where
     γ₁ : (p : P) (q : Q) → (p , q) ∙× ε[ ℂ ] ＝ (p , q)
     γ₁ p q = (p , q) ∙× ε[ ℂ ]                ＝⟨ refl ⟩
              (p ·₁ ε[ ℂ ]) , (q ·₂ ε[ ℂ ])    ＝⟨ †    ⟩
              p , (q ·₂ ε[ ℂ ])                ＝⟨ ‡    ⟩
              p , q                            ∎
               where
                † = ap (_, (q ·₂ ε[ ℂ ])) (action-preserves-unit ℂ 𝒫 p)
                ‡ = ap (p ,_) (action-preserves-unit ℂ 𝒬 q)

     γ₂ : (r : P × Q) (u v : ⟪ ℂ ⟫) → r ∙× (u *[ ℂ ] v) ＝ (r ∙× u) ∙× v
     γ₂ (p , q) u v =
      (p , q) ∙× (u *[ ℂ ] v)                 ＝⟨ refl ⟩
      p ·₁ (u *[ ℂ ] v) , q ·₂ (u *[ ℂ ] v)   ＝⟨ †    ⟩
      (p ·₁ u) ·₁ v , q ·₂ (u *[ ℂ ] v)       ＝⟨ ‡    ⟩
      (p ·₁ u) ·₁ v , (q ·₂ u) ·₂ v           ＝⟨ refl ⟩
      ((p , q) ∙× u) ∙× v                     ∎
       where
        † = ap (_, q ·₂ (u *[ ℂ ] v)) (actions-are-functorial ℂ 𝒫 p u v)
        ‡ = ap ((p ·₁ u) ·₁ v ,_) (actions-are-functorial ℂ 𝒬 q u v)

   𝒶 : [ ℂ ]-action-on ((P × Q) , ×-is-set σ₁ σ₂)
   𝒶 = _∙×_ , γ

   ℛ : [ ℂ ]-set (𝓤 ⊔ 𝓥)
   ℛ = ((P × Q) , ×-is-set σ₁ σ₂) , 𝒶

   ♠ : is-sheaf ℛ holds
   ♠ i 𝒿 = ((p , q) , φ) , ψ
    where
     open EqualityCombinator P σ₁ renaming (_＝ₛ_ to _＝₁_)
     open EqualityCombinator Q σ₂ renaming (_＝ₛ_ to _＝₂_)

     𝒿₁ = pr₁ ∘ 𝒿
     𝒿₂ = pr₂ ∘ 𝒿

     ♥₁ : (!∃ p ∶ P , Ɐ s ∶ Vec 𝟚 i , p ·₁ (𝔠𝔬𝔫𝔰 s) ＝₁ 𝒿₁ s) holds
     ♥₁ = ♠₁ i (pr₁ ∘ 𝒿)

     p : P
     p = pr₁ (center ♥₁)

     ♥₂ : (!∃ q ∶ Q , Ɐ s ∶ Vec 𝟚 i , q ·₂ (𝔠𝔬𝔫𝔰 s) ＝₂ 𝒿₂ s) holds
     ♥₂ = ♠₂ i (pr₂ ∘ 𝒿)

     q : Q
     q = pr₁ (center ♥₂)

     φ₁ : (s : Vec 𝟚 i) → p ·₁ (𝔠𝔬𝔫𝔰 s) ＝ 𝒿₁ s
     φ₁ = pr₂ (pr₁ ♥₁)

     φ₂ : (s : Vec 𝟚 i) → q ·₂ (𝔠𝔬𝔫𝔰 s) ＝ 𝒿₂ s
     φ₂ = pr₂ (pr₁ ♥₂)

     φ : (s : Vec 𝟚 i) → ((p , q) ∙× (𝔠𝔬𝔫𝔰 s)) ＝ 𝒿₁ s , 𝒿₂ s
     φ s = to-×-＝ (φ₁ s) (φ₂ s)

     ψ : is-central
          (Σ (p , q) ꞉ (P × Q) ,
            ((s : Vec 𝟚 i) → (p , q) ∙× (𝔠𝔬𝔫𝔰 s) ＝ 𝒿 s))
          ((p , q) , φ)
     ψ ((p′ , q′) , φ′) = to-subtype-＝ ※ (to-×-＝ †₁ †₂)
      where
       φ′₁ : (s : Vec 𝟚 i) → p′ ·₁ (𝔠𝔬𝔫𝔰 s) ＝ 𝒿₁ s
       φ′₁ s = pr₁ (from-×-＝' (φ′ s))

       φ′₂ : (s : Vec 𝟚 i) → q′ ·₂ (𝔠𝔬𝔫𝔰 s) ＝ 𝒿₂ s
       φ′₂ s = pr₂ (from-×-＝' (φ′ s))

       ξ₁ : p , φ₁ ＝ p′ , φ′₁
       ξ₁ = centrality ♥₁ (p′ , φ′₁)

       †₁ : p ＝ p′
       †₁ = pr₁ (from-Σ-＝ ξ₁)

       ξ₂ : q , φ₂ ＝ q′ , φ′₂
       ξ₂ = centrality ♥₂ (q′ , φ′₂)

       †₂ : q ＝ q′
       †₂ = pr₁ (from-Σ-＝ ξ₂)

       ※ : (r : P × Q)
         → is-prop ((s : Vec 𝟚 i) → (r ∙× 𝔠𝔬𝔫𝔰 s) ＝ 𝒿 s)
       ※ r = Π-is-prop fe (λ _ → ×-is-set σ₁ σ₂)

\end{code}

\begin{code}

_€_ : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓥  ̇} → ((A → B) × C) → A → B
_€_ p = p .pr₁

infixr 5 _€_

π₁ : (P Q : Sheaf 𝓤) → ℋℴ𝓂 (P ×ₛ Q) P
π₁ 𝒫 𝒬 = pr₁ , ν
 where
  ν : is-natural′ (𝒫 ×ₛ 𝒬) 𝒫 pr₁ holds
  ν u v = refl

π₂ : (P Q : Sheaf 𝓤) → ℋℴ𝓂 (P ×ₛ Q) Q
π₂ 𝒫 𝒬 = pr₂ , ν
 where
  ν : is-natural′ (𝒫 ×ₛ 𝒬) 𝒬 pr₂ holds
  ν u v = refl

pair : (O P Q : Sheaf 𝓤) → ℋℴ𝓂 O P → ℋℴ𝓂 O Q → ℋℴ𝓂 O (P ×ₛ Q)
pair 𝒪 𝒫 𝒬 ρ₁ ρ₂ = 𝒻 , ν
 where
  𝒻 : ∣ 𝒪 ∣ₛ → ∣ 𝒫 ×ₛ 𝒬 ∣ₛ
  𝒻 o = apply 𝒪 𝒫 ρ₁ o , apply 𝒪 𝒬 ρ₂ o

  ν : is-natural′ 𝒪 (𝒫 ×ₛ 𝒬) 𝒻 holds
  ν o u =
   𝒻 (μ ℂ (pr₁ 𝒪) o u)                                    ＝⟨ refl ⟩
   ρ₁ .pr₁ (μ ℂ (pr₁ 𝒪) o u) , ρ₂ .pr₁ (μ ℂ (pr₁ 𝒪) o u)  ＝⟨ I    ⟩
   μ ℂ (pr₁ 𝒫) (ρ₁ .pr₁ o) u , ρ₂ .pr₁ (μ ℂ (pr₁ 𝒪) o u)  ＝⟨ II   ⟩
   μ ℂ (pr₁ 𝒫) (ρ₁ .pr₁ o) u , μ ℂ (pr₁ 𝒬) (ρ₂ .pr₁ o) u   ∎
    where
     I  = ap (λ - → - , ρ₂ .pr₁ (μ ℂ (pr₁ 𝒪) o u)) (pr₂ ρ₁ o u)
     II = ap (λ - → μ ℂ (pr₁ 𝒫) (ρ₁ .pr₁ o) u , -) (pr₂ ρ₂ o u)

\end{code}
