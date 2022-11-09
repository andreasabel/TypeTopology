\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import MLTT.Fin

module UniformContinuityTopos.Sheaf
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe

open import UniformContinuityTopos.Coverage pt fe ℂ

open PropositionalTruncation pt

\end{code}

\begin{code}


\end{code}
