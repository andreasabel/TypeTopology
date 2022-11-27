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
open import UF.Powerset

open Universal fe
open Conjunction
open Implication fe

open monoid

\end{code}

\begin{code}

⟪_⟫ : Monoid {𝓤} → 𝓤  ̇
⟪ A , _ ⟫ = A

ε[_] : (M : Monoid {𝓤}) → ⟪ M ⟫
ε[ _ , (_ , 𝟏) , _ ] = 𝟏

monoid-op-syntax : (M : Monoid {𝓤}) → ⟪ M ⟫ → ⟪ M ⟫ → ⟪ M ⟫
monoid-op-syntax (_ , (_∙_ , _) , _) = _∙_

syntax monoid-op-syntax M x y = x *[ M ] y

ε[_]-is-left-unit : (M : Monoid {𝓤}) (x : ⟪ M ⟫) → ε[ M ] *[ M ] x ＝ x
ε[_]-is-left-unit (_ , _ , (_ , p , _)) = p

ε[_]-is-right-unit : (M : Monoid {𝓤}) (x : ⟪ M ⟫) → x *[ M ] ε[ M ] ＝ x
ε[_]-is-right-unit (_ , _ , (_ , _ , q , r)) = q

*[_]-is-associative : (M : Monoid {𝓤})
                    → (x y z : ⟪ M ⟫)
                    → (x *[ M ] y) *[ M ] z ＝ x *[ M ] (y *[ M ] z)
*[_]-is-associative M x y z = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ M)))) x y z

monoid-carrier-is-set : (M : Monoid {𝓤}) → is-set ⟪ M ⟫
monoid-carrier-is-set (_ , _ , (σ , _)) = σ

is-[_]-action : {A : 𝓥  ̇} (M : Monoid {𝓤}) → is-set A → (A → ⟪ M ⟫ → A) → Ω (𝓥 ⊔ 𝓤)
is-[_]-action {𝓥 = 𝓥} {𝓤} {A} M@(_ , (_*_ , ε) , _) σ _·_ = β ∧ γ
 where
  open EqualityCombinator A σ

  β : Ω 𝓥
  β = Ɐ x ∶ A , x · ε ＝ₛ x

  γ : Ω (𝓤 ⊔ 𝓥)
  γ = Ɐ x ∶ A , Ɐ u ∶ ⟪ M ⟫ , Ɐ v ∶ ⟪ M ⟫ , x · (u * v) ＝ₛ (x · u) · v

[_]-action-on : Monoid {𝓤} → hSet 𝓥 → 𝓤 ⊔ 𝓥  ̇
[ M ]-action-on (A , σ) = Σ _·_ ꞉ (A → ⟪ M ⟫ → A) , (is-[ M ]-action σ _·_ holds)

[_]-set : Monoid {𝓤} → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺  ̇
[_]-set {𝓤} M 𝓥 = Σ A ꞉ hSet 𝓥 , [ M ]-action-on A

carrier : (M : Monoid {𝓤}) → [ M ]-set 𝓥 → 𝓥  ̇
carrier M ((P , _) , _·_) = P

μ : (M : Monoid {𝓤}) → (P : [ M ]-set 𝓥) → carrier M P → ⟪ M ⟫ → carrier M P
μ M (P , _∙_ , _) = _∙_

action-preserves-unit : (M : Monoid {𝓤}) (P : [ M ]-set 𝓥)
                      → (x : carrier M P) → μ M P x ε[ M ] ＝ x
action-preserves-unit M (P , _ , (p , _)) = p

actions-are-functorial : (M : Monoid {𝓤}) (𝒫 : [ M ]-set 𝓥)
                       → (x : carrier M 𝒫) (u v : ⟪ M ⟫)
                       → μ M 𝒫 x (u *[ M ] v) ＝ μ M 𝒫 (μ M 𝒫 x u) v
actions-are-functorial M (P , _ , (_ , q)) = q

\end{code}

\begin{code}

self-action : (M : Monoid {𝓤}) → [ M ]-set 𝓤
self-action M = (⟪ M ⟫ , monoid-carrier-is-set M) , _·_ , †
 where
  _·_ : ⟪ M ⟫ → ⟪ M ⟫ → ⟪ M ⟫
  u · v = u *[ M ] v

  † : is-[ M ]-action (monoid-carrier-is-set M) _·_ holds
  † = β , γ
   where
    β : (u : ⟪ M ⟫) → u · ε[ M ] ＝ u
    β = ε[ M ]-is-right-unit

    γ : (u v w : ⟪ M ⟫) → u · (v · w) ＝ (u · v) · w
    γ u v w = *[ M ]-is-associative u v w ⁻¹

\end{code}

\begin{code}

is-right-ideal : (M : Monoid {𝓤}) → 𝓟 ⟪ M ⟫ → Ω 𝓤
is-right-ideal M S = Ɐ x ∶ ⟪ M ⟫ , Ɐ u ∶ ⟪ M ⟫ , S x ⇒ S (x *[ M ] u)

\end{code}
