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
        (M   : Monoid {𝓤})
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Coverage pt fe M
open import UniformContinuityTopos.Sheaf pt fe M
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt

\end{code}

\begin{code}

module DefnOfΩ (𝒸ℴ𝓋 : Coverage 𝓦) where

 open DefnOfSheaf 𝒸ℴ𝓋

 -- TODO: to be implemented.
 postulate Ωₛ : Sheaf

\end{code}
