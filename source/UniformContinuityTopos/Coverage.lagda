\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import MLTT.List hiding ([_])

open import UF.SIP-Examples
open monoid

module UniformContinuityTopos.Coverage
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (M  : Monoid {𝓤})
        where

open import UF.Subsingletons

open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.MonoidAction fe

open import UF.Subsingleton-Combinators

open Universal fe
open Existential pt fe

\end{code}

\section{Preliminaries}

\begin{code}

Fam : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
Fam 𝓤 A = Σ I ꞉ (𝓤 ̇) , (I → A)

fmap-syntax : {A : 𝓤 ̇} {B : 𝓥 ̇}
            → (A → B) → Fam 𝓦 A → Fam 𝓦 B
fmap-syntax h (I , f) = I , h ∘ f

infix 2 fmap-syntax

syntax fmap-syntax (λ x → e) U = ⁅ e ∣ x ε U ⁆

compr-syntax : {A : 𝓤 ̇} (I : 𝓦 ̇) → (I → A) → Fam 𝓦 A
compr-syntax I f = I , f

infix 2 compr-syntax

syntax compr-syntax I (λ x → e) = ⁅ e ∣ x ∶ I ⁆

index : {A : 𝓥  ̇} → Fam 𝓦 A  → 𝓦  ̇
index (I , _) = I

_[_] : {A : 𝓥  ̇} → (U : Fam 𝓦 A) → index U → A
(_ , f) [ i ] = f i

infix 14 _[_]

\end{code}

\begin{code}

_*_ : ⟪ M ⟫ → ⟪ M ⟫ → ⟪ M ⟫
_*_ = pr₁ (pr₁ (pr₂ M))

open EqualityCombinator ⟪ M ⟫ (monoid-carrier-is-set M)

is-coverage : Fam 𝓦 (Fam 𝓦 ⟪ M ⟫) → Ω (𝓤 ⊔ 𝓦)
is-coverage 𝒥 = Ɐ u ∶ ⟪ M ⟫ , Ɐ i ∶ index 𝒥 ,
                 Ǝ̃ j ∶ index 𝒥 ,
                  Ɐ s ∶ index (𝒥 [ j ]) ,
                   Ǝ̃ v ∶ ⟪ M ⟫ , Ǝ̃ s′ ∶ index (𝒥 [ i ]) ,
                    u * (𝒥 [ j ] [ s ]) ＝ₛ (𝒥 [ i ] [ s′ ]) * v

Coverage : (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺  ̇
Coverage 𝓦 = Σ 𝒥 ꞉ Fam 𝓦 (Fam 𝓦 ⟪ M ⟫) , is-coverage 𝒥 holds

\end{code}
