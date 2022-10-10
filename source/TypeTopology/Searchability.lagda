\begin{code}

module TypeTopology.Searchability where

open import MLTT.Spartan
open import UF.Base
open import TypeTopology.TotallySeparated
open import TypeTopology.CompactTypes
open import MLTT.NaturalNumbers
open import MLTT.Unit
open import MLTT.Sigma using (uncurry)
open import UF.FunExt

\end{code}

\begin{code}

module Experiment (X : 𝓤  ̇) (fe : funext 𝓤₀ 𝓤) (κ : compact∙ X) where

 tail : (ℕ → X) → (ℕ → X)
 tail u = u ∘ succ

 head : (ℕ → X) → X
 head u = u 0

 cons : X → (ℕ → X) → (ℕ → X)
 cons x α zero     = x
 cons x α (succ i) = α i

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

 cons-decreases-mod-of-uc : (p : (ℕ → X) → 𝟚)
                          → (n : ℕ)
                          → (succ n) is-a-mod-of-uc-of p
                          → (x : X) → n is-a-mod-of-uc-of (p ∘ cons x)
 cons-decreases-mod-of-uc p n φ x u v eq = φ (cons x u) (cons x v) (refl , eq)

 cons-head-tail : (α : ℕ → X) → cons (head α) (tail α) ＝ α
 cons-head-tail α = dfunext fe h
  where
   h : cons (head α) (tail α) ∼ α
   h zero     = refl
   h (succ i) = refl

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

  X-is-compact∙' : compact∙' X
  X-is-compact∙' = compact∙-gives-compact∙' κ

  ϵX : (X → 𝟚) → X
  ϵX = pr₁ X-is-compact∙'

  ϵX-is-selection-functional : (p : X → 𝟚)
                             → p (ϵX p) ＝ ₁
                             → (x : X) → p x ＝ ₁
  ϵX-is-selection-functional = pr₂ X-is-compact∙'

  ∀X : (X → 𝟚) → 𝟚
  ∀X p = p (ϵX p)

  ∀X-spec→ : (p : X → 𝟚)
           → ∀X p ＝ ₁
           → (x : X) → p x ＝ ₁
  ∀X-spec→ = ϵX-is-selection-functional

  ∀X-spec← : (p : X → 𝟚)
           → ((x : X) → p x ＝ ₁)
           → ∀X p ＝ ₁
  ∀X-spec← p φ = φ (ϵX p)

  ϵₙ : ℕ → ((ℕ → X) → 𝟚) → (ℕ → X)
  ∀ₙ : ℕ → ((ℕ → X) → 𝟚) → 𝟚

  ϵₙ zero     p = λ _ → x₀
  ϵₙ (succ n) p = cons y₀ (ϵₙ n (λ α → p (cons y₀ α)))
    where
      y₀ = ϵX λ x → ∀ₙ n (λ α → p (cons x α))

  ∀ₙ n p = p (ϵₙ n p)

  ∀ₙ-satisfies-spec₂ : (p : (ℕ → X) → 𝟚)
                     → (n : ℕ)
                     → (ζ : n is-a-mod-of-uc-of p)
                     → ((u : ℕ → X) → p u ＝ ₁)
                     → ∀ₙ n p ＝ ₁
  ∀ₙ-satisfies-spec₂ p n ζ φ = φ (ϵₙ n p)

  ∀ₙ-satisfies-spec₁ : (p : (ℕ → X) → 𝟚)
                     → (n : ℕ)
                     → (ζ : n is-a-mod-of-uc-of p)
                     → ∀ₙ n p ＝ ₁
                     → (u : ℕ → X) → p u ＝ ₁
  ∀ₙ-satisfies-spec₁ p zero     ψ φ u =
   p u          ＝⟨ † ⟩
   p (λ _ → x₀) ＝⟨ φ ⟩
   ₁            ∎
    where
     † = mod-of-uc-zero-means-constant p ψ u (λ _ → x₀)
  ∀ₙ-satisfies-spec₁ p (succ k) ψ φ u =
   p u                        ＝⟨ ap p (cons-head-tail u) ⁻¹ ⟩
   p (cons (head u) (tail u)) ＝⟨ † ⟩
   ₁                          ∎
    where
     x₁ : X
     x₁ = ϵX (λ y → ∀ₙ k (p ∘ cons y))

     ♠ : ∀ₙ k (p ∘ cons x₁) ＝ ₁ → (x : X) → ∀ₙ k (p ∘ cons x) ＝ ₁
     ♠ = ∀X-spec→ (λ y → ∀ₙ k (p ∘ cons y))

     IH : (x : X) → ∀ₙ k (p ∘ cons x) ＝ ₁ → (v : ℕ → X) → p (cons x v) ＝ ₁
     IH x = ∀ₙ-satisfies-spec₁ (p ∘ cons x) k (cons-decreases-mod-of-uc p k ψ x)

     ♥ : (x : X) (v : ℕ → X) → p (cons x v) ＝ ₁
     ♥ x = IH x (♠ φ x)

     † : p (cons (head u) (tail u)) ＝ ₁
     † = ♥ (head u) (tail u)

  Xᴺ-is-compact : (p : (ℕ → X) → 𝟚)
                → is-locally-constant p
                → Σ u₀ ꞉ (ℕ → X) , (p u₀ ＝ ₁ → (u : ℕ → X) → p u ＝ ₁)
  Xᴺ-is-compact p υ@(n , ζ) = ϵₙ n p , ∀ₙ-satisfies-spec₁ p n ζ

\end{code}
