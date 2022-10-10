\begin{code}

module TypeTopology.Searchability where

open import MLTT.Spartan
open import UF.Base
open import TypeTopology.TotallySeparated
open import TypeTopology.CompactTypes
open import MLTT.NaturalNumbers
open import MLTT.Unit
open import MLTT.Sigma using (uncurry)

\end{code}

\begin{code}

module Experiment (X : 𝓤  ̇) (σ : is-totally-separated X) (κ : compact∙ X) where

 tail : (ℕ → X) → (ℕ → X)
 tail u = u ∘ succ

 head : (ℕ → X) → X
 head u = u 0

\end{code}

Equality up to some `n`:

\begin{code}

 _=[_]=_ : (ℕ → X) → ℕ → (ℕ → X) → 𝓤  ̇
 u =[ zero   ]= v = 𝟙
 u =[ succ n ]= v = (head u ＝ head v) × (tail u =[ n ]= tail v)

\end{code}

\begin{code}

 _is-a-mod-of-uc-of_ : ℕ → ((ℕ → X) → 𝟚) → 𝓤  ̇
 n is-a-mod-of-uc-of p = (u v : ℕ → X) → u =[ n ]= v → p u ＝ p v

 is-locally-constant : ((ℕ → X) → 𝟚) → 𝓤  ̇
 is-locally-constant p = Σ n ꞉ ℕ , n is-a-mod-of-uc-of p

 _∷_ : X → (ℕ → X) → ℕ → X
 (x ∷ u) zero     = x
 (x ∷ u) (succ i) = u i

 cons-decreases-mod-of-uc : (p : (ℕ → X) → 𝟚)
                          → (n : ℕ)
                          → (succ n) is-a-mod-of-uc-of p
                          → (x : X) → n is-a-mod-of-uc-of (p ∘ x ∷_)
 cons-decreases-mod-of-uc p n φ x u v eq = φ (x ∷ u) (x ∷ v) (refl , eq)

 cons-head-tail : {!!}
 cons-head-tail = {!!}

\end{code}

\begin{code}

 is-constant : ((ℕ → X) → 𝟚) → 𝓤  ̇
 is-constant p = (u v : ℕ → X) → p u ＝ p v

 mod-of-uc-zero-means-constant : (p : (ℕ → X) → 𝟚)
                               → 0 is-a-mod-of-uc-of p
                               → is-constant p
 mod-of-uc-zero-means-constant p ζ u v = ζ u v ⋆

 constant-means-has-mod-of-uc-zero : (p : (ℕ → X) → 𝟚)
                                   → is-constant p
                                   → 0 is-a-mod-of-uc-of p
 constant-means-has-mod-of-uc-zero p ζ u v ⋆ = ζ u v

\end{code}

\begin{code}

 module Search (x₀ : X) where

  ϵX : (X → 𝟚) → X
  ϵX = pr₁ (compact∙-gives-compact∙' κ)

  ϵₙ : ℕ → ((ℕ → X) → 𝟚) → (ℕ → X)
  ∀ₙ : ℕ → ((ℕ → X) → 𝟚) → 𝟚

  ϵₙ zero     p = λ _ → x₀
  ϵₙ (succ n) p = y₀ ∷ ϵₙ n (λ α → p (y₀ ∷ α))
    where
      y₀ = ϵX λ x → ∀ₙ n (λ α → p (x ∷ α))

  ∀ₙ n p = p (ϵₙ n p)

  ∀ₙ-satisfies-spec₁ : (p : (ℕ → X) → 𝟚)
                     → ((n , _) : is-locally-constant p)
                     → ∀ₙ n p ＝ ₁
                     → (u : ℕ → X) → p u ＝ ₁
  ∀ₙ-satisfies-spec₁ p (n , ζ) = † n ζ
   where
    † : (n : ℕ)
      → n is-a-mod-of-uc-of p
      → ∀ₙ n p ＝ ₁ → (u : ℕ → X) → p u ＝ ₁
    † zero     ζ φ u = p u          ＝⟨ mod-of-uc-zero-means-constant p ζ u (λ _ → x₀) ⟩
                       p (λ _ → x₀) ＝⟨ φ ⟩
                       ₁            ∎
    † (succ n) ζ φ u = p u                ＝⟨ {!!} ⟩
                       p (ϵₙ (succ n) p)  ＝⟨ refl ⟩
                       ∀ₙ (succ n) p      ＝⟨ φ ⟩
                       ₁                  ∎

  ∀ₙ-satisfies-spec₂ : (p : (ℕ → X) → 𝟚)
                     → ((n , _) : is-locally-constant p)
                     → ((u : ℕ → X) → p u ＝ ₁)
                     → ∀ₙ n p ＝ ₁
  ∀ₙ-satisfies-spec₂ p (n , ζ) φ = φ (ϵₙ n p)

  Xᴺ-is-compact : (p : (ℕ → X) → 𝟚)
                → is-locally-constant p
                → Σ u₀ ꞉ (ℕ → X) , (p u₀ ＝ ₁ → (u : ℕ → X) → p u ＝ ₁)
  Xᴺ-is-compact p υ@(n , ζ) = ϵₙ n p , ∀ₙ-satisfies-spec₁ p υ

\end{code}
