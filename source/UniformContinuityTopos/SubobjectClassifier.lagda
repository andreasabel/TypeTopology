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

module UniformContinuityTopos.SubobjectClassifier
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.UniformContinuityCoverage pt fe
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Sheaf pt fe
open import UF.Subsingletons-FunExt
open import UF.Retracts
open import UF.Powerset

open PropositionalTruncation pt

\end{code}

\begin{code}

ℳ : hSet 𝓤₀
ℳ = ⟪ ℂ ⟫ , monoid-carrier-is-set ℂ

is-set₀ : 𝓤  ̇ → Ω 𝓤
is-set₀ X = is-set X , being-set-is-prop fe

Fam₀ : (𝓦 : Universe) → hSet 𝓥 → 𝓥 ⊔ 𝓦 ⁺  ̇
Fam₀ 𝓦 (A , _) = Σ I ꞉ hSet 𝓦 , (pr₁ I → A)

-- TODO: to be implemented.
postulate Ωₛ : Sheaf 𝓤₁

\end{code}
