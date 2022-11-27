\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.Miscelanea
open import UF.UA-FunExt
open import UF.Size
open import MLTT.Fin

open import UF.SIP-Examples
open monoid

module UniformContinuityTopos.SubobjectClassifier
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (𝕡𝕣  : propositional-resizing 𝓤₁ 𝓤₀)
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
open import UF.Size

open PropositionalTruncation pt

\end{code}

\begin{code}

ℳ : hSet 𝓤₀
ℳ = ⟪ ℂ ⟫ , monoid-carrier-is-set ℂ

is-set₀ : 𝓤  ̇ → Ω 𝓤
is-set₀ X = is-set X , being-set-is-prop fe

Fam₀ : (𝓦 : Universe) → hSet 𝓥 → 𝓥 ⊔ 𝓦 ⁺  ̇
Fam₀ 𝓦 (A , _) = Σ I ꞉ hSet 𝓦 , (pr₁ I → A)

foo : {A : 𝓤₀  ̇} → (S : 𝓟 A) → (x : A) → (S x) holds is 𝓤₀ small
foo S x = (S x holds) , {!!}
 where
  † : {!!}
  † = 𝕡𝕣 {!S!} {!!}

𝓟′ : {𝓤 : Universe} → 𝓤₀  ̇ → 𝓤₀  ̇
𝓟′ A = {!!}
 where
  † : {!!}
  † = 𝕡𝕣 (𝓟 A) {!!}

∣Ω∣ : 𝓤₀  ̇
∣Ω∣ = {!!}

-- TODO: to be implemented.
Ωₛ : Sheaf 𝓤₀
Ωₛ = ((∣Ω∣ , {!!}) , {!!}) , {!!}

\end{code}
