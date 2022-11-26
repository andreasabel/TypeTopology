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
open import UF.Subsingletons-FunExt
open import Naturals.Order using (max)
open import Naturals.Properties

open PropositionalTruncation pt
open EqualityCombinator ⟪ ℂ ⟫ (monoid-carrier-is-set ℂ)

\end{code}

\section{Definition of sheaf over the UC site}

\begin{code}

thread : (𝟚 → ⟪ ℂ ⟫) → Cantor → Cantor
thread 𝓉 α = ⦅ 𝓉 (head α) ⦆ (tail α)

\end{code}

Thread is a uniformly continuous function.

\begin{code}

thread-uniformly-continuous : (𝓉 : 𝟚 → ⟪ ℂ ⟫)
                            → is-uniformly-continuous (thread 𝓉) holds
thread-uniformly-continuous 𝓉 m =
 ∥∥-rec₂ (holds-is-prop Ψ) γ (pr₂ (𝓉 ₀) m) (pr₂ (𝓉 ₁) m)
  where
   Ψ = Ǝ̃ n ∶ ℕ , Ɐ α ∶ Cantor , Ɐ β ∶ Cantor , α ＝⟦ n ⟧ β ⇒ thread 𝓉 α ＝⟦ m ⟧ thread 𝓉 β

   γ : Σ n₀ ꞉ ℕ , (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor ,
                    α ＝⟦ n₀ ⟧ β ⇒ ⦅ 𝓉 ₀ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₀ ⦆ β) holds
     → Σ n₁ ꞉ ℕ , (Ɐ α ∶ Cantor , Ɐ β ∶ Cantor ,
                    α ＝⟦ n₁ ⟧ β ⇒ ⦅ 𝓉 ₁ ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 ₁ ⦆ β) holds
     → (Ǝ̃ n ∶ ℕ , Ɐ α ∶ Cantor , Ɐ β ∶ Cantor ,
         α ＝⟦ n ⟧ β ⇒ thread 𝓉 α ＝⟦ m ⟧ thread 𝓉 β) holds
   γ (n₀ , ϕ₀) (n₁ , ϕ₁) = {!!}

 --   γ (n₀ , ϕ₀) (n₁ , ϕ₁) = ∣ n , † ∣
 --    where
 --     n = succ (max n₀ n₁)

 --     † : (α β : Cantor) → (α ＝⟦ n ⟧ β ⇒ ⦅ 𝓉 (head α) ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 (head β) ⦆ β) holds
 --     † α β p = ♠ (head α) (head β) refl refl
 --      where
 --       ♠ : (x y : 𝟚) → x ＝ head α → y ＝ head β → (⦅ 𝓉 x ⦆ α ＝⟦ m ⟧ ⦅ 𝓉 y ⦆ β) holds
 --       ♠ ₀ ₀ _ _ = ϕ₀ α β (pr₁ (＝-max-lemma α β n₀ n₁ (＝-pred-lemma {n = max n₀ n₁} α β p)))
 --       ♠ ₀ ₁ q r = 𝟘-elim (positive-not-zero (max n₀ n₁) (≠-head-tail α β n p ϟ))
 --                    where
 --                     ϟ : ¬ (head α ＝ head β)
 --                     ϟ eq = zero-is-not-one (₀       ＝⟨ q    ⟩
 --                                             head α  ＝⟨ eq   ⟩
 --                                             head β  ＝⟨ r ⁻¹ ⟩
 --                                             ₁       ∎)
 --       ♠ ₁ ₀ q r = 𝟘-elim (positive-not-zero (max n₀ n₁) (≠-head-tail α β n p ϟ))
 --                    where
 --                     ϟ : ¬ (head α ＝ head β)
 --                     ϟ eq = one-is-not-zero (₁      ＝⟨ q    ⟩
 --                                             head α ＝⟨ eq   ⟩
 --                                             head β ＝⟨ r ⁻¹ ⟩
 --                                             ₀      ∎)
 --       ♠ ₁ ₁ _ _ = ϕ₁ α β (pr₂ (＝-max-lemma α β n₀ n₁ (＝-pred-lemma {n = max n₀ n₁} α β p)))

\end{code}

\begin{code}

𝔱𝔥𝔯𝔢𝔞𝔡 : (𝟚 → ⟪ ℂ ⟫) → ⟪ ℂ ⟫
𝔱𝔥𝔯𝔢𝔞𝔡 𝓉 = thread 𝓉 , thread-uniformly-continuous 𝓉

\end{code}

\begin{code}

self-action-is-sheaf : is-sheaf (self-action ℂ) holds
self-action-is-sheaf = sheaf′-implies-sheaf (self-action ℂ) ※
 where
  ※ : is-sheaf′ (self-action ℂ) holds
  ※ n 𝓉 = (𝔱𝔥𝔯𝔢𝔞𝔡 𝓉 , †) , c
   where
    † : (b : 𝟚) → 𝔱𝔥𝔯𝔢𝔞𝔡 𝓉 ⊚ 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 b ＝ 𝓉 b
    † ₀ = UC-Endomap-extensional-equality λ _ → refl
    † ₁ = UC-Endomap-extensional-equality λ _ → refl

    c : is-central (Σ t ꞉ ⟪ ℂ ⟫ , ((b : 𝟚) → t ⊚ 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 b ＝ 𝓉 b)) (𝔱𝔥𝔯𝔢𝔞𝔡 𝓉 , †)
    c (t , †′) =
     to-subtype-＝ (λ _ → Π-is-prop fe λ _ → monoid-carrier-is-set ℂ) ♠
      where
       γ : (b : 𝟚) (α : Cantor) → thread 𝓉 (⦅ 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 b ⦆ α)  ＝ ⦅ 𝓉 b ⦆ α
       γ b α = ap (λ - → - α) (pr₁ (from-Σ-＝ († b)))

       γ′ : (b : 𝟚) (α : Cantor) → ⦅ t ⊚ 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 b ⦆ α ＝ ⦅ 𝓉 b ⦆  α
       γ′ b α = ap (λ - → - α) (pr₁ (from-Σ-＝ (†′ b)))

       ♢ : (α : Cantor) (x : 𝟚) → x ＝ head α → ⦅ 𝓉 x ⦆ (tail α) ＝ ⦅ t ⦆ α
       ♢ α b p = ⦅ 𝓉 b ⦆ (tail α)                    ＝⟨ ap (λ - → ⦅ 𝓉 - ⦆ (tail α)) p ⟩
                 ⦅ 𝓉 (head α) ⦆ (tail α)             ＝⟨ γ′ (head α) (tail α) ⁻¹ ⟩
                 ⦅ t ⊚ 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 (head α) ⦆ (tail α)  ＝⟨ refl ⟩
                 ⦅ t ⊚ 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 (head α) ⦆ (tail α)  ＝⟨ ap ⦅ t ⦆ (cons-bit-tail-lemma α) ⟩
                 ⦅ t ⦆ α                             ∎

       ♠ : 𝔱𝔥𝔯𝔢𝔞𝔡 𝓉 ＝ t
       ♠ = UC-Endomap-extensional-equality (λ α → ♢ α (head α) refl)


\end{code}
