\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import MLTT.List hiding ([_])

module UniformContinuityTopos.Presheaf
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        where

open import UF.Subsingletons

open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.MonoidAction fe

\end{code}

A presheaf over the uniform continuity topos is just a `ℂ`-set.

\begin{code}

Presheaf : 𝓤₁  ̇
Presheaf = [ ℂ ]-set

\end{code}
