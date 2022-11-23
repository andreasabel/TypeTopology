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
 ∥∥-rec₂ (holds-is-prop Ψ) γ (pr₂ (𝓉 ₀) m) (pr₂ (𝓉 ₁) m)
  where
   Ψ = Ǝ̃ n ∶ ℕ , Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ n ⟧ β ⇒ thread 𝓉 α ＝⟦ m ⟧ thread 𝓉 β
   γ : Σ n₀ ꞉ ℕ , (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ n₀ ⟧ β ⇒ ⦅ 𝓉 ₀ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₀ ⦆ β) holds
     → Σ n₁ ꞉ ℕ , (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ n₁ ⟧ β ⇒ ⦅ 𝓉 ₁ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₁ ⦆ β) holds
     → (Ǝ̃ n ∶ ℕ , Ɐ α ∶ Cantor , Ɐ β ∶ Cantor ,
         α ＝⟦ n ⟧ β ⇒ thread 𝓉 α ＝⟦ m ⟧ thread 𝓉 β) holds
   γ (n₀ , ϕ₀) (n₁ , ϕ₁) = ∣ n , † ∣
    where
     n = succ (max n₀ n₁)

     † : (α β : Cantor) → (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 (head α) ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 (head β) ⦆ β) holds
     † α β p = ♠ (head α) (head β) refl refl
      where
       ♠ : (x y : 𝟚) → x ＝ head α → y ＝ head β → (⦅ 𝓉 x ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 y ⦆ β) holds
       ♠ ₀ ₀ _ _ = ϕ₀ α β (pr₁ (＝-max-lemma α β n₀ n₁ (＝-pred-lemma {n = max n₀ n₁} α β p)))
       ♠ ₀ ₁ q r = 𝟘-elim (positive-not-zero (max n₀ n₁) (≠-head-tail α β n p ϟ))
                    where
                     ϟ : ¬ (head α ＝ head β)
                     ϟ eq = zero-is-not-one (₀       ＝⟨ q    ⟩
                                             head α  ＝⟨ eq   ⟩
                                             head β  ＝⟨ r ⁻¹ ⟩
                                             ₁       ∎)
       ♠ ₁ ₀ q r = 𝟘-elim (positive-not-zero (max n₀ n₁) (≠-head-tail α β n p ϟ))
                    where
                     ϟ : ¬ (head α ＝ head β)
                     ϟ eq = one-is-not-zero (₁      ＝⟨ q    ⟩
                                             head α ＝⟨ eq   ⟩
                                             head β ＝⟨ r ⁻¹ ⟩
                                             ₀      ∎)
       ♠ ₁ ₁ _ _ = ϕ₁ α β (pr₂ (＝-max-lemma α β n₀ n₁ (＝-pred-lemma {n = max n₀ n₁} α β p)))

𝔱𝔥𝔯𝔢𝔞𝔡 : (𝟚 → ⟪ ℂ ⟫) → UC-Endomap
𝔱𝔥𝔯𝔢𝔞𝔡 𝓉 = thread 𝓉 , thread-uniformly-continuous 𝓉

𝔱𝔥𝔯𝔢𝔞𝔡⋆ : {k : ℕ} → (Vec 𝟚 k → ⟪ ℂ ⟫) → UC-Endomap
𝔱𝔥𝔯𝔢𝔞𝔡⋆ {zero}   𝓉 = 𝓉 []
𝔱𝔥𝔯𝔢𝔞𝔡⋆ {succ n} 𝓉 = 𝔱𝔥𝔯𝔢𝔞𝔡⋆ (λ s → 𝔱𝔥𝔯𝔢𝔞𝔡 (λ b → 𝓉 (b ∷ s)))

self-action-is-sheaf : is-sheaf (self-action ℂ) holds
self-action-is-sheaf = †
 where
  † : (k : ℕ) (𝓉 : Vec 𝟚 k → ⟪ ℂ ⟫)
    → (!∃ p ∶ ⟪ ℂ ⟫ , Ɐ s ∶ Vec 𝟚 k , p ⊚ 𝔠𝔬𝔫𝔰 s ＝ₛ 𝓉 s) holds
  † k 𝓉 = (𝔱𝔥𝔯𝔢𝔞𝔡⋆ 𝓉 , ♠) , {!!}
   where
    ♠ : (s : Vec 𝟚 k) → 𝔱𝔥𝔯𝔢𝔞𝔡⋆ 𝓉 ⊚ 𝔠𝔬𝔫𝔰 s ＝ 𝓉 s
    ♠ s = {!!}

self : Sheaf 𝓤₀
self = {!!} -- self-action ℂ , self-action-is-sheaf

\end{code}
