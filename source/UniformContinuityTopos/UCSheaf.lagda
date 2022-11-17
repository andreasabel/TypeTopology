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

open AllCombinators pt fe

open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Coverage pt fe ℂ
open import UniformContinuityTopos.Sheaf pt fe ℂ

open PropositionalTruncation pt

open DefnOfSheaf

\end{code}

\section{Definition of sheaf over the UC site}

\begin{code}

is-uc-sheaf : [ ℂ ]-set → Ω {!!}
is-uc-sheaf = {!!}

UCSheaf : {!!}
UCSheaf = {!!}

self-action-is-sheaf′ : is-sheaf (self-action ℂ) holds
self-action-is-sheaf′ = ?


\end{code}
