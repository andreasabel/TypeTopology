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

open PropositionalTruncation pt
open EqualityCombinator ⟪ ℂ ⟫ (monoid-carrier-is-set ℂ)

\end{code}

\section{Definition of sheaf over the UC site}

\begin{code}

thread : (𝟚 → ⟪ ℂ ⟫) → Cantor → Cantor
thread 𝓉 α = ⦅ 𝓉 (head α) ⦆ α

\end{code}

\begin{code}

_＝₂_ : 𝟚 → 𝟚 → Ω 𝓤₀
₀ ＝₂ ₀ = ⊤Ω
₁ ＝₂ ₁ = ⊥Ω
₀ ＝₂ ₁ = ⊥Ω
₁ ＝₂ ₀ = ⊤Ω

thread-uniformly-continuous : (𝓉 : 𝟚 → ⟪ ℂ ⟫)
                            → is-uniformly-continuous (thread 𝓉) holds
thread-uniformly-continuous 𝓉 m =
 ∥∥-rec₂ {!!} γ (pr₂ (𝓉 ₀) m) (pr₂ (𝓉 ₁) m)
  where
   γ : Σ n₀ ꞉ ℕ , (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ n₀ ⟧ β ⇒ ⦅ 𝓉 ₀ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₀ ⦆ β) holds
     → Σ n₁ ꞉ ℕ , (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ n₁ ⟧ β ⇒ ⦅ 𝓉 ₁ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₁ ⦆ β) holds
     → (Ǝ̃ n ∶ ℕ , Ɐ α ∶ Cantor , Ɐ β ∶ Cantor ,
         α ＝⟦ n ⟧ β ⇒ thread 𝓉 α ＝⟦ m ⟧ thread 𝓉 β) holds
   γ (n₀ , ϕ₀) (n₁ , ϕ₁) = ∣ n , † ∣
    where
     n = succ (max n₀ n₁)

     † : (α β : Cantor) → (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 (head α) ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 (head β) ⦆ β) holds
     † α β p = ※ (head α) (head β) refl refl
      where
       ※ : (x y : 𝟚) → x ＝ head α → y ＝ head β → (⦅ 𝓉 x ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 y ⦆ β) holds
       ※ ₀ ₀ _ _ = ϕ₀ α β (pr₁ (＝-max-lemma α β n₀ n₁ (＝-pred-lemma {n = max n₀ n₁} α β p)))
       ※ ₀ ₁ q r = 𝟘-elim (zero-is-not-one {!!})
       ※ ₁ ₀ q r = 𝟘-elim {!!}
       ※ ₁ ₁ _ _ = ϕ₁ α β (pr₂ (＝-max-lemma α β n₀ n₁ (＝-pred-lemma {n = max n₀ n₁} α β p)))
      --  A = λ - → (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 - ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 (head β) ⦆ β) holds

      --  †₀ : (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 ₀ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 (head β) ⦆ β) holds
      --  †₀ = 𝟚-induction {A = B} ‡₀ ‡₁ (head β)
      --   where
      --    B = λ - → (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 ₀ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 - ⦆ β) holds

      --    ‡₀ : (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 ₀ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₀ ⦆ β) holds
      --    ‡₀ p = ϕ₀ α β (pr₁ (＝-max-lemma α β n₀ n₁ (＝-pred-lemma {n = max n₀ n₁} α β p)))

      --    ‡₁ : (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 ₀ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₁ ⦆ β) holds
      --    ‡₁ p = {!!}

      --  †₁ : (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 ₁ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 (head β) ⦆ β) holds
      --  †₁ = {!!}

self-action-is-sheaf : is-sheaf (self-action ℂ) holds
self-action-is-sheaf = †
 where
  † : (k : ℕ) (𝓉 : Vec 𝟚 k → ⟪ ℂ ⟫)
    → (!∃ p ∶ ⟪ ℂ ⟫ , Ɐ s ∶ Vec 𝟚 k , p ⊚ 𝔠𝔬𝔫𝔰 s ＝ₛ 𝓉 s) holds
  † k 𝓉 = (𝓅 , {!!}) , {!!}
   where
    p : Cantor → Cantor
    p α = ⦅ 𝓉 (take k α) ⦆ α
     where
      q : Cantor → Cantor
      q = ⦅ 𝓉 (take k α) ⦆

    κ : (s : Vec 𝟚 k) → is-uniformly-continuous ⦅ 𝓉 s ⦆ holds
    κ s = pr₂ (𝓉 s)

    ζ : is-uniformly-continuous p holds
    ζ m = ∣ k , ‡ ∣
     where
      ‡ : (α β : Cantor) → (α ＝⟦ k ⟧ β) holds → (p α ＝⟦ m ⟧ p β) holds
      ‡ α β ϕ = ∥∥-rec (holds-is-prop (p α ＝⟦ m ⟧ p β)) ♠ (κ (take k α) m)
       where
        ♠ : (Σ n ꞉ ℕ , ((β₀ β₁ : Cantor) → (β₀ ＝⟦ n ⟧ β₁ ⇒ ⦅ 𝓉 (take k α) ⦆ β₀ ＝⟦ m ⟧ ⦅ 𝓉 (take k α) ⦆ β₁) holds))
          → (⦅ 𝓉 (take k α) ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 (take k β) ⦆ β) holds
        ♠ (n , ψ) = ※
         where
          ※ : (⦅ 𝓉 (take k α) ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 (take k β) ⦆ β) holds
          ※ = transport
               (λ - → (⦅ 𝓉 (take k α) ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 - ⦆ β) holds)
               (take-＝-lemma k α β ϕ)
               (ψ α β {!!})


    𝓅 : ⟪ ℂ ⟫
    𝓅 = {!!} ⊚ {!𝔱𝔞𝔨𝔢!}

self : Sheaf 𝓤₀
self = self-action ℂ , self-action-is-sheaf

\end{code}
