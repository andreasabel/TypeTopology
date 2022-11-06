Ayberk Tosun, 5 November 2022

Based on Chuangjie Xu's formalisation.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import MLTT.List hiding ([_])

module UniformContinuityTopos.UniformContinuityMonoid
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        where

open import UF.Subsingletons
open import UF.Miscelanea
open import UF.Retracts
open import UF.Subsingletons-FunExt
open import UF.Subsingleton-Combinators
open import UF.SIP-Examples

open PropositionalTruncation pt

open AllCombinators pt fe

\end{code}

\begin{code}

Cantor : 𝓤₀  ̇
Cantor = ℕ → 𝟚

Cantor-is-set : is-set Cantor
Cantor-is-set = Π-is-set fe λ _ → 𝟚-is-set

open EqualityCombinator 𝟚 𝟚-is-set

\end{code}

Some preliminary operations on the Cantor space.

\begin{code}

head : Cantor → 𝟚
head α = α 0

tail : Cantor → Cantor
tail α = α ∘ succ

_＝⟦_⟧_ : Cantor → ℕ → Cantor → Ω 𝓤₀
α ＝⟦ 0      ⟧ β = ⊤Ω
α ＝⟦ succ n ⟧ β = α 0 ＝ₛ β 0 ∧ tail α ＝⟦ n ⟧ tail β

\end{code}

Definition of uniform continuity of an endomap of the Cantor space.

\begin{code}

is-uniformly-continuous : (Cantor → Cantor) → Ω 𝓤₀
is-uniformly-continuous t =
 Ɐ m ∶ ℕ ,
  Ǝ n ∶ ℕ ,
   (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ n ⟧ β ⇒ t α ＝⟦ m ⟧ t β) holds

UC-Endomap : 𝓤₀  ̇
UC-Endomap = Σ t ꞉ (Cantor → Cantor) , is-uniformly-continuous t holds

\end{code}

Conventient shorthand for the first projection:

\begin{code}

⦅_⦆ : UC-Endomap → Cantor → Cantor
⦅ t , _ ⦆ = t

\end{code}

\begin{code}

UC-Endomap-extensional-equality : {𝓉₁ 𝓉₂ : UC-Endomap}
                                → ((α : Cantor) → ⦅ 𝓉₁ ⦆ α ＝ ⦅ 𝓉₂ ⦆ α)
                                → 𝓉₁ ＝ 𝓉₂
UC-Endomap-extensional-equality {𝓉₁} {𝓉₂} φ = to-subtype-＝ β γ
 where
  β : (t : Cantor → Cantor) → is-prop (is-uniformly-continuous t holds)
  β = holds-is-prop ∘ is-uniformly-continuous

  γ : ⦅ 𝓉₁ ⦆ ＝ ⦅ 𝓉₂ ⦆
  γ = dfunext fe φ

\end{code}

\begin{code}

open monoid

id-is-uniformly-continuous : is-uniformly-continuous id holds
id-is-uniformly-continuous m = ∣ m , † ∣
 where
  † : (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ m ⟧ β ⇒ α ＝⟦ m ⟧ β) holds
  † α β p = p

𝔦𝔡 : UC-Endomap
𝔦𝔡 = id , id-is-uniformly-continuous

∘-is-uniformly-continuous : (t₁ t₂ : Cantor → Cantor)
                          → is-uniformly-continuous t₁ holds
                          → is-uniformly-continuous t₂ holds
                          → is-uniformly-continuous (t₂ ∘ t₁) holds
∘-is-uniformly-continuous t₁ t₂ ζ₁ ζ₂ m = ∥∥-rec ∃-is-prop † (ζ₂ m)
 where
  † : Σ n₂ ꞉ ℕ , (Ɐ α , Ɐ β , α ＝⟦ n₂ ⟧ β ⇒ t₂ α ＝⟦ m ⟧ t₂ β) holds
    → ∃ n ꞉ ℕ , (Ɐ α , Ɐ β , α ＝⟦ n ⟧ β ⇒ t₂ (t₁ α) ＝⟦ m ⟧ t₂ (t₁ β)) holds
  † (n₂ , φ) = ∥∥-rec ∃-is-prop ‡ (ζ₁ n₂)
   where
    ‡ : Σ n₁ ꞉ ℕ , (Ɐ α , Ɐ β , α ＝⟦ n₁ ⟧ β ⇒ t₁ α ＝⟦ n₂ ⟧ t₁ β) holds
      → ∃ n ꞉ ℕ , (Ɐ α , Ɐ β , α ＝⟦ n ⟧ β ⇒ t₂ (t₁ α) ＝⟦ m ⟧ t₂ (t₁ β)) holds
    ‡ (n₁ , ψ) = ∣ n₁ , ※ ∣
     where
      ※ : (Ɐ α , Ɐ β , α ＝⟦ n₁ ⟧ β ⇒ t₂ (t₁ α) ＝⟦ m ⟧ t₂ (t₁ β)) holds
      ※ α β p = φ (t₁ α) (t₁ β) (ψ α β p)

_⊚_ : UC-Endomap → UC-Endomap → UC-Endomap
(t₂ , ζ₂) ⊚ (t₁ , ζ₁) = t₂ ∘ t₁ , ∘-is-uniformly-continuous t₁ t₂ ζ₁ ζ₂

ℂ-monoid-structure : monoid-structure UC-Endomap
ℂ-monoid-structure = _⊚_ , 𝔦𝔡

\end{code}

\begin{code}

ℂ-satisfies-monoid-axioms : monoid-axioms UC-Endomap ℂ-monoid-structure
ℂ-satisfies-monoid-axioms = σ , ι₁ , ι₂ , γ
 where
  σ : is-set UC-Endomap
  σ = Σ-is-set
       (Π-is-set fe (λ _ → Cantor-is-set))
       λ _ → props-are-sets (holds-is-prop (is-uniformly-continuous _))

  ι₁ : left-neutral 𝔦𝔡 _⊚_
  ι₁ 𝓉 = UC-Endomap-extensional-equality λ _ → refl

  ι₂ : right-neutral 𝔦𝔡 _⊚_
  ι₂ 𝓉 = UC-Endomap-extensional-equality λ _ → refl

  γ : associative _⊚_
  γ 𝓉₁ 𝓉₂ 𝓉₃ = UC-Endomap-extensional-equality λ _ → refl

\end{code}

\begin{code}

ℂ : Monoid
ℂ = UC-Endomap , ℂ-monoid-structure , ℂ-satisfies-monoid-axioms

\end{code}
