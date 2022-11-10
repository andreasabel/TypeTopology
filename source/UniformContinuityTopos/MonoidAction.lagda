\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import MLTT.List hiding ([_])

module UniformContinuityTopos.MonoidAction
        (fe : Fun-Ext)
        where

open import UF.Subsingletons
-- open import UF.Miscelanea
-- open import UF.Retracts
-- open import UF.Subsingletons-FunExt
open import UF.Subsingleton-Combinators
open import UF.SIP-Examples

open Universal fe
open Conjunction

open monoid

\end{code}

\begin{code}

⟪_⟫ : Monoid {𝓤} → 𝓤  ̇
⟪ A , _ ⟫ = A

monoid-carrier-is-set : (M : Monoid {𝓤}) → is-set ⟪ M ⟫
monoid-carrier-is-set (_ , _ , (σ , _)) = σ

is-[_]-action : {A : 𝓤  ̇} (M : Monoid {𝓤}) → is-set A → (A → ⟪ M ⟫ → A) → Ω 𝓤
is-[_]-action {𝓤} {A} M@(_ , (_*_ , ε) , _) σ _·_ = β ∧ γ
 where
  open EqualityCombinator A σ

  β : Ω 𝓤
  β = Ɐ x ∶ A , x · ε ＝ₛ x

  γ : Ω 𝓤
  γ = Ɐ x ∶ A , Ɐ u ∶ ⟪ M ⟫ , Ɐ v ∶ ⟪ M ⟫ , x · (u * v) ＝ₛ (x · u) · v

[_]-action-on : Monoid {𝓤} → hSet 𝓤 → 𝓤  ̇
[ M ]-action-on (A , σ) = Σ _·_ ꞉ (A → ⟪ M ⟫ → A) , (is-[ M ]-action σ _·_ holds)

[_]-set : Monoid {𝓤} → 𝓤 ⁺  ̇
[_]-set {𝓤} M = Σ A ꞉ hSet 𝓤 , [ M ]-action-on A

¡_¡ : {A : 𝓤  ̇} {M : Monoid {𝓤}} → [ M ]-set → 𝓤  ̇
¡_¡ ((P , _) , _) = P

\end{code}
