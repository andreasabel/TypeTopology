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
        (M   : Monoid {𝓤 ⁺})
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Sheaf pt fe
open import UF.Subsingletons-FunExt
open import UF.Retracts
open import UF.Powerset

open PropositionalTruncation pt

\end{code}

\begin{code}

module DefnOfΩ where

 ℳ : hSet (𝓤 ⁺)
 ℳ = ⟪ M ⟫ , monoid-carrier-is-set M

 is-set₀ : 𝓤  ̇ → Ω 𝓤
 is-set₀ X = is-set X , being-set-is-prop fe

 Fam₀ : (𝓦 : Universe) → hSet 𝓥 → 𝓥 ⊔ 𝓦 ⁺  ̇
 Fam₀ 𝓦 (A , _) = Σ I ꞉ hSet 𝓦 , (pr₁ I → A)

 is-right-ideal : Fam₀ 𝓤 ℳ → Ω (𝓤 ⁺)
 is-right-ideal ((I , _) , f) =
  Ɐ i ∶ I , Ɐ u ∶ ⟪ M ⟫ , Ǝ̃ j ∶ I , f j ＝ₛ u *[ M ] f i
   where
    open EqualityCombinator ⟪ M ⟫ (monoid-carrier-is-set M)

 RightIdeal : 𝓤 ⁺  ̇
 RightIdeal = Σ S ꞉ Fam₀ 𝓤 ℳ , is-right-ideal S holds

 -- RightIdeal₀ : hSet (𝓤 ⁺)
 -- RightIdeal₀ = RightIdeal , †
 --  where
 --   † : is-set RightIdeal
 --   † = Σ-is-set {!!} {!!}

 -- _·_ : RightIdeal → ⟪ M ⟫ → RightIdeal
 -- S · u = {!!}

 -- TODO: to be implemented.
 postulate Ωₛ : Sheaf 𝓤₁

\end{code}
