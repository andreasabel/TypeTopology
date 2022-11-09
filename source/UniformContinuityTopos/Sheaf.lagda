\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import MLTT.Fin

open import UF.SIP-Examples
open monoid

module UniformContinuityTopos.Sheaf
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (M   : Monoid {𝓤})
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Coverage pt fe M

open PropositionalTruncation pt

\end{code}

\begin{code}

module DefnOfSheaf (𝒸ℴ𝓋 : Coverage 𝓦) where

 𝒥             = pr₁ 𝒸ℴ𝓋
 𝒥-is-coverage = pr₂ 𝒸ℴ𝓋

 is-sheaf : [ M ]-set → Ω (𝓤 ⊔ 𝓦)
 is-sheaf ((P , s) , _·_ , ν) =
  Ɐ i ∶ index 𝒥 , Ɐ 𝒿 ∶ (index (𝒥 [ i ]) → P) ,
   !∃ p ∶ P ,
    Ɐ s ∶ index (𝒥 [ i ]) , p · (𝒥 [ i ] [ s ]) ＝ₛ 𝒿 s
     where
      open EqualityCombinator P s

\end{code}
