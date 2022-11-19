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
open import UniformContinuityTopos.UniformContinuityCoverage pt fe
open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Coverage pt fe ℂ
open import UniformContinuityTopos.Sheaf pt fe ℂ

open PropositionalTruncation pt

\end{code}

\section{Definition of sheaf over the UC site}

\begin{code}

open DefnOfSheaf UC-coverage renaming (Sheaf to UC-Sheaf)
open EqualityCombinator ⟪ ℂ ⟫ (monoid-carrier-is-set ℂ)

thread : (𝟚 → ⟪ ℂ ⟫) → Cantor → Cantor
thread 𝓉 α = ⦅ 𝓉 (head α) ⦆ α

thread-uniformly-continuous : (𝓉 : 𝟚 → ⟪ ℂ ⟫)
                            → is-uniformly-continuous (thread 𝓉) holds
thread-uniformly-continuous 𝓉 m =
 ∥∥-rec (holds-is-prop {!!}) γ (pr₂ (𝓉 ₀) m)
  where
   γ : (Σ n ꞉ ℕ , (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 ₀ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₀ ⦆ β) holds)
     → (Ǝ̃ n ∶ ℕ , Ɐ α ∶ Cantor , Ɐ β ∶ Cantor ,
         α ＝⟦ n ⟧ β ⇒ thread 𝓉 α ＝⟦ m ⟧ thread 𝓉 β) holds
   γ (n , ϕ) = ∣ n , † ∣
    where
     † : (β₁ β₂ : Cantor) → (β₁ ＝⟦ n ⟧ β₂ ⇒ thread 𝓉 β₁ ＝⟦ m ⟧ thread 𝓉 β₂) holds
     † β₁ β₂ p = {!!}

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

self : UC-Sheaf
self = self-action ℂ , {!!}

\end{code}
