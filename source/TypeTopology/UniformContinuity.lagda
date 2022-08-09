\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import TypeTopology.DiscreteAndSeparated
open import Naturals.Order
open import Notation.Order

open import UF.FunExt
open import UF.Base

module TypeTopology.UniformContinuity (fe : funext 𝓤₀ 𝓤₀) where

open import TypeTopology.CantorSearch fe

\end{code}

\begin{code}

is-mn-uc : (Cantor → Cantor) → Type
is-mn-uc f =
 Π m ꞉ ℕ , Σ n ꞉ ℕ , Π α ꞉ Cantor , Π β ꞉ Cantor , (α ＝⟦ n ⟧ β → f α ＝⟦ m ⟧ f β)

reflexivity : (α : Cantor) (n : ℕ) → α ＝⟦ n ⟧ α
reflexivity α zero     = ⋆
reflexivity α (succ n) = refl , reflexivity (α ∘ succ) n

is-locally-constant : {X : 𝓤  ̇} → (Cantor → X) → 𝓤  ̇
is-locally-constant f = Σ n ꞉ ℕ , Π α ꞉ Cantor , Π β ꞉ Cantor , (α ＝⟦ n ⟧ β → f α ＝ f β)

_⦅_,─⦆ : {A B C : 𝓤  ̇} → (A × B → C) → A → B → C
f ⦅ x ,─⦆ = λ y → f (x , y)

_⦅─,_⦆ : {A B C : 𝓤  ̇} → (A × B → C) → B → A → C
f ⦅─, y ⦆ = λ x → f (x , y)

\end{code}


\begin{code}

mn-uc-lemma₀ : (f : Cantor × Cantor → Cantor)
            → ((α : Cantor) → is-locally-constant (f ⦅ α ,─⦆))
            → ((β : Cantor) → is-locally-constant (f ⦅─, β ⦆))
            → (α₁ β₁ α₂ β₂ : Cantor)
            → Σ n₁ ꞉ ℕ , Σ n₂ ꞉ ℕ , (α₁ ＝⟦ n₁ ⟧ β₁ → α₂ ＝⟦ n₂ ⟧ β₂ → f (α₁ , α₂) ＝ f (β₁ , β₂))
mn-uc-lemma₀ f φ ψ α₁ α₂ β₁ β₂ = n₂ , n₁ , †
 where
  n₁ : ℕ
  n₁ = pr₁ (φ α₂)

  n₂ : ℕ
  n₂ = pr₁ (ψ β₁)

  ♥ : α₁ ＝⟦ n₂ ⟧ α₂ → f (α₁ , β₁) ＝ f (α₂ , β₁)
  ♥ = pr₂ (ψ β₁) α₁ α₂

  ♣ : β₁ ＝⟦ n₁ ⟧ β₂ → f (α₂ , β₁) ＝ f (α₂ , β₂)
  ♣ = pr₂ (φ α₂) β₁ β₂

  † : α₁ ＝⟦ n₂ ⟧ α₂ → β₁ ＝⟦ n₁ ⟧ β₂ → f (α₁ , β₁) ＝ f (α₂ , β₂)
  † p q = f (α₁ , β₁)  ＝⟨ ♥ p ⟩
          f (α₂ , β₁)  ＝⟨ ♣ q ⟩
          f (α₂ , β₂)  ∎

-- TODO: think about this.
-- mn-uc-lemma₁ : (f : Cantor × Cantor → Cantor)
--              → ((α : Cantor) → is-locally-constant (f ⦅ α ,─⦆))
--              → ((β : Cantor) → is-locally-constant (f ⦅─, β ⦆))
--              → (Σ n₁ ꞉ ℕ , Σ n₂ ꞉ ℕ ,
--                  ((α₁ β₁ α₂ β₂ : Cantor) → (α₁ ＝⟦ n₁ ⟧ α₂ → β₁ ＝⟦ n₂ ⟧ β₂ → f (α₁ , β₁) ＝ f (α₂ , β₂))))
-- mn-uc-lemma₁ f φ ψ = n₁ , n₂ , †

mn-uc-lemma₂ : (f : Cantor × Cantor → Cantor)
             → (Σ n₁ ꞉ ℕ , Σ n₂ ꞉ ℕ ,
                 ((α₁ β₁ α₂ β₂ : Cantor) → (α₁ ＝⟦ n₁ ⟧ α₂ → β₁ ＝⟦ n₂ ⟧ β₂ → f (α₁ , β₁) ＝ f (α₂ , β₂))))
             → (α β : Cantor) → is-locally-constant (f ⦅ α ,─⦆) × is-locally-constant (f ⦅─, β ⦆)
mn-uc-lemma₂ f ψ α β = † , ‡
 where
  n₁ : ℕ
  n₁ = pr₁ ψ

  n₂ : ℕ
  n₂ = pr₁ (pr₂ ψ)

  η : Π β₁ ꞉ Cantor , Π β₂ ꞉ Cantor , (β₁ ＝⟦ n₂ ⟧ β₂ → f (α , β₁) ＝ f (α , β₂))
  η β₁ β₂ p = pr₂ (pr₂ ψ) α β₁ α β₂ (reflexivity α n₁) p

  θ : Π α₁ ꞉ Cantor , Π α₂ ꞉ Cantor , (α₁ ＝⟦ n₁ ⟧ α₂ → f (α₁ , β) ＝ f (α₂ , β))
  θ α₁ α₂ p = pr₂ (pr₂ ψ) α₁ β α₂ β p (reflexivity β n₂)

  † : is-locally-constant (f ⦅ α ,─⦆)
  † = n₂ , η

  ‡ : is-locally-constant (f ⦅─, β ⦆)
  ‡ = n₁ , θ

\end{code}
