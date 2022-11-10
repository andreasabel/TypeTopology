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

module UniformContinuityTopos.InternalLanguage
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (M   : Monoid {𝓤})
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators
open AllCombinators pt fe

open import UniformContinuityTopos.Coverage pt fe M

\end{code}

\begin{code}

open import UniformContinuityTopos.Sheaf pt fe M

module DefnOfInternalLanguage (𝒸ℴ𝓋 : Coverage 𝓦) where

 open DefnOfSheaf 𝒸ℴ𝓋

 𝒯𝓎𝓅ℯ : 𝓤 ⁺ ⊔ 𝓦  ̇
 𝒯𝓎𝓅ℯ = Sheaf

 private
  variable
   X Y : 𝒯𝓎𝓅ℯ

 data 𝒞𝓉𝓍 : 𝓤 ⁺ ⊔ 𝓦  ̇ where
  ∅    : 𝒞𝓉𝓍
  _⌢_  : 𝒞𝓉𝓍 → 𝒯𝓎𝓅ℯ → 𝒞𝓉𝓍

 infix  4 _∋_
 infixl 5 _⌢_

 private
  variable
   Γ Δ : 𝒞𝓉𝓍

 data _∋_ : 𝒞𝓉𝓍 → 𝒯𝓎𝓅ℯ → 𝓤  ̇ where
  here  : Γ ⌢ X ∋ X
  there : Γ ∋ X → Γ ⌢ Y ∋ X

 data _⊢_ : 𝒞𝓉𝓍 → 𝒯𝓎𝓅ℯ → 𝓤  ̇ where
  var : Γ ∋ X → Γ ⊢ X

 mutual

  ⟦_⟧ₜ : 𝒞𝓉𝓍 → Sheaf
  ⟦ ∅     ⟧ₜ = 𝟏ₛ
  ⟦ Γ ⌢ X ⟧ₜ = ⟦ Γ ⟧ₜ ×ₛ X

  ⟦_⟧ₓ : Γ ∋ X → ℋℴ𝓂 ⟦ Γ ⟧ₜ X
  ⟦_⟧ₓ {.(_ ⌢ X)} {X} here      = {!𝟏[ X ]!}
  ⟦_⟧ₓ {.(_ ⌢ _)} {X} (there t) = {!!}

  ⟦_⟧ : Γ ⊢ X → ℋℴ𝓂 ⟦ Γ ⟧ₜ X
  ⟦_⟧ {Γ = (_ ⌢ X)} {X} (var here) = {!!}
  ⟦_⟧ {Γ = .(_ ⌢ _)} {X} (var (there x)) = {!!}

\end{code}
