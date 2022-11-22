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
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators
open AllCombinators pt fe

open import UniformContinuityTopos.SubobjectClassifier pt fe
open import UniformContinuityTopos.Product pt fe

\end{code}

\begin{code}

open import UniformContinuityTopos.Sheaf pt fe

𝒯𝓎𝓅ℯ : (𝓤 : Universe) → 𝓤 ⁺  ̇
𝒯𝓎𝓅ℯ 𝓤 = Sheaf 𝓤

private
 variable
  X Y : 𝒯𝓎𝓅ℯ 𝓤

data 𝒞𝓉𝓍 : Universe → 𝓤ω where
 ∅    : 𝒞𝓉𝓍 𝓤₀
 _⌢_  : {𝓤 𝓥 : Universe} → 𝒞𝓉𝓍 𝓤 → 𝒯𝓎𝓅ℯ 𝓥 → 𝒞𝓉𝓍 (𝓤 ⊔ 𝓥)

infix  4 _∋_
infixl 5 _⌢_

private
 variable
  Γ Δ : 𝒞𝓉𝓍 𝓤

data _∋_ : 𝒞𝓉𝓍 𝓤 → 𝒯𝓎𝓅ℯ 𝓥 → 𝓤ω where
 here  : {𝓤 : Universe} {Γ : 𝒞𝓉𝓍 𝓤} → Γ ⌢ X ∋ X
 there : {𝓤 : Universe} {Γ : 𝒞𝓉𝓍 𝓤} → Γ ∋ X → Γ ⌢ Y ∋ X

data _⊢_ : 𝒞𝓉𝓍 𝓤 → 𝒯𝓎𝓅ℯ 𝓤 → 𝓤ω where
 var  : Γ ∋ X → Γ ⊢ X
 _,ᵢ_ : Γ ⊢ X → Γ ⊢ Y → Γ ⊢ (X ×ₛ Y)
 _∘ᵢ_ : ℋℴ𝓂 X Y → Γ ⊢ X → Γ ⊢ Y

⟦_⟧ₜ : 𝒞𝓉𝓍 𝓤 → Sheaf 𝓤
⟦ ∅     ⟧ₜ = 𝟏ₛ
⟦ Γ ⌢ X ⟧ₜ = ⟦ Γ ⟧ₜ ×ₛ X

⟦_⟧ₓ : {𝓤 : Universe} {Γ : 𝒞𝓉𝓍 𝓤} {X : 𝒯𝓎𝓅ℯ 𝓤} → Γ ∋ X → ℋℴ𝓂 ⟦ Γ ⟧ₜ X
⟦ t ⟧ₓ = {!!}

{--


  𝓉𝓎𝓅ℯ-ℴ𝒻 : Γ ⊢ X → 𝒯𝓎𝓅ℯ
  𝓉𝓎𝓅ℯ-ℴ𝒻 {_} {X} t = X


  ⟦_⟧ : Γ ⊢ X → ℋℴ𝓂 ⟦ Γ ⟧ₜ X
  ⟦_⟧ {Γ}     (var i)            = ⟦ i ⟧ₓ
  ⟦_⟧ {Γ}     (t₁ ,ᵢ t₂)         = pair ⟦ Γ ⟧ₜ (𝓉𝓎𝓅ℯ-ℴ𝒻 t₁) (𝓉𝓎𝓅ℯ-ℴ𝒻 t₂) ⟦ t₁ ⟧ ⟦ t₂ ⟧
  ⟦_⟧ {Γ} {X} (_∘ᵢ_ {Z} {X} f t) = comp ⟦ Γ ⟧ₜ Z X f ⟦ t ⟧
--}

\end{code}
