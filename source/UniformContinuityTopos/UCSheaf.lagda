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

module UniformContinuityTopos.UCSheaf
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators
open import MLTT.Two-Properties

open AllCombinators pt fe

open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.UniformContinuityCoverage pt fe
open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Sheaf pt fe
open import Naturals.Order using (max)
open import Naturals.Properties

open PropositionalTruncation pt
open EqualityCombinator ⟪ ℂ ⟫ (monoid-carrier-is-set ℂ)

\end{code}

\section{Definition of sheaf over the UC site}

\begin{code}

\end{code}
