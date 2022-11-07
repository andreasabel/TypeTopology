\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import MLTT.List hiding ([_])
open import MLTT.Fin

module UniformContinuityTopos.Sheaf
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        where

open import UF.Subsingletons

open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Coverage pt fe ℂ

open PropositionalTruncation pt

\end{code}

\begin{code}

cons : List 𝟚 → Cantor → Cantor
cons []      α          = α
cons (b ∷ b⃗) α zero     = b
cons (b ∷ b⃗) α (succ i) = cons b⃗ α i

length : List 𝟚 → ℕ
length []      = 0
length (b ∷ s) = succ (length s)

cons-uniformly-continuous : (s : List 𝟚) → is-uniformly-continuous (cons s) holds
cons-uniformly-continuous []      m = ∣ 0 , † ∣
 where
  † : {!!}
  † = {!!}
cons-uniformly-continuous (b ∷ s) m = {!!}

𝒥 : Fam 𝓤₀ ⟪ ℂ ⟫
𝒥 = List 𝟚 , 𝒻
 where
  𝒻 : List 𝟚 → ⟪ ℂ ⟫
  𝒻 s = cons s , cons-uniformly-continuous s

\end{code}
