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
open import MLTT.List hiding ([_]; _∷_)

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
open import UniformContinuityTopos.Vector

open PropositionalTruncation pt

open AllCombinators pt fe

\end{code}

The _Cantor type_ is the type of Boolean sequences:

\begin{code}

Cantor : 𝓤₀  ̇
Cantor = ℕ → 𝟚

Cantor-is-set : is-set Cantor
Cantor-is-set = Π-is-set fe λ _ → 𝟚-is-set

\end{code}

Some preliminary operations on the Cantor space.

\begin{code}

open EqualityCombinator 𝟚 𝟚-is-set

head : Cantor → 𝟚
head α = α 0

tail : Cantor → Cantor
tail α = α ∘ succ

_＝⟦_⟧_ : Cantor → ℕ → Cantor → Ω 𝓤₀
α ＝⟦ 0      ⟧ β = ⊤Ω
α ＝⟦ succ n ⟧ β = α 0 ＝ₛ β 0 ∧ tail α ＝⟦ n ⟧ tail β

\end{code}

Definition of uniform continuity of an endomap of the Cantor space:

\begin{code}

is-uniformly-continuous : (Cantor → Cantor) → Ω 𝓤₀
is-uniformly-continuous t =
 Ɐ m ∶ ℕ , Ǝ̃ n ∶ ℕ , Ɐ α , Ɐ β , α ＝⟦ n ⟧ β ⇒ t α ＝⟦ m ⟧ t β

\end{code}

We denote by `UC-Endomap` the type of _uniformly continuous endomaps_ on the
Cantor space:

\begin{code}

UC-Endomap : 𝓤₀  ̇
UC-Endomap = Σ t ꞉ (Cantor → Cantor) , is-uniformly-continuous t holds

\end{code}

Given an inhabitant `𝓉` of `UC-Endomap`, `⦅ 𝓉 ⦆` denotes the underlying function
of `𝓉`:

\begin{code}

⦅_⦆ : UC-Endomap → Cantor → Cantor
⦅ t , _ ⦆ = t

\end{code}

Two inhabitants `𝓉₁, 𝓉₂ : UC-Endomap` are equal whenever `⦅ 𝓉₁ ⦆` and `⦅ 𝓉₂ ⦆`
are extensionally equal. We record this fact in
`UC-Endomap-extensional-equality`:

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

\section{Definition of the monoid ℂ}

We first prove that the identity map `id` is uniformly continuous:

\begin{code}

id-is-uniformly-continuous : is-uniformly-continuous id holds
id-is-uniformly-continuous m = ∣ m , † ∣
 where
  † : (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ m ⟧ β ⇒ α ＝⟦ m ⟧ β) holds
  † α β p = p

\end{code}

In accordance with our convention of using 𝔣𝔯𝔞𝔨𝔱𝔲𝔯 letters for inhabitants of
`UC-Endomap`, we define `𝔦𝔡` to be the identity uniformly continuous endomap:

\begin{code}

𝔦𝔡 : UC-Endomap
𝔦𝔡 = id , id-is-uniformly-continuous

\end{code}

We now prove that the composition of two uniformly continuous endomaps are
uniformly continuous:

\begin{code}

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

\end{code}

We can now define a composition operator on the type `UC-Endomap` directly:

\begin{code}

infixl 12 _⊚_

_⊚_ : UC-Endomap → UC-Endomap → UC-Endomap
(t₂ , ζ₂) ⊚ (t₁ , ζ₁) = t₂ ∘ t₁ , ∘-is-uniformly-continuous t₁ t₂ ζ₁ ζ₂

\end{code}

The operator `_⊚_` together with `𝔦𝔡` is a monoid structure:

\begin{code}

open monoid

ℂ-monoid-structure : monoid-structure UC-Endomap
ℂ-monoid-structure = _⊚_ , 𝔦𝔡

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

Finally, we define `ℂ` to be the monoid of uniformly continuous endomaps on the
Cantor space:

\begin{code}

ℂ : Monoid
ℂ = UC-Endomap , ℂ-monoid-structure , ℂ-satisfies-monoid-axioms

\end{code}

\section{Some operations on the Cantor space}

\begin{code}

take : (n : ℕ) → Cantor → Vec 𝟚 n
take zero     α = []
take (succ n) α = α 0 ∷ take n (tail α)

tail-is-uniformly-continuous : is-uniformly-continuous tail holds
tail-is-uniformly-continuous zero     = ∣ 0             , (λ _ _ _ → ⋆) ∣
tail-is-uniformly-continuous (succ m) = ∣ succ (succ m) , ζ (succ m)    ∣
 where
  ζ : (n : ℕ) (α β : Cantor) → (α ＝⟦ succ n ⟧ β ⇒ tail α ＝⟦ n ⟧ tail β) holds
  ζ n α β (p , q) = q

𝔱𝔞𝔦𝔩 : UC-Endomap
𝔱𝔞𝔦𝔩 = tail , tail-is-uniformly-continuous

drop : ℕ → Cantor → Cantor
drop zero     = id
drop (succ n) = drop n ∘ tail

drop-is-uniformly-continuous : (n : ℕ) → is-uniformly-continuous (drop n) holds
drop-is-uniformly-continuous zero     = id-is-uniformly-continuous
drop-is-uniformly-continuous (succ n) =
 ∘-is-uniformly-continuous tail (drop n) tail-is-uniformly-continuous ℐℋ
  where
   ℐℋ : is-uniformly-continuous (drop n) holds
   ℐℋ = drop-is-uniformly-continuous n

𝔡𝔯𝔬𝔭 : ℕ → UC-Endomap
𝔡𝔯𝔬𝔭 n = drop n , drop-is-uniformly-continuous n

\end{code}
