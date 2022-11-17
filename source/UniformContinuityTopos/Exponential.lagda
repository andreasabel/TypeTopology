---
title: Exponentials of Sheaves
author: Ayberk Tosun
date: 15 November 2022
---

\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.Miscelanea
open import UF.UA-FunExt
open import MLTT.Fin

open import UF.SIP-Examples
open monoid

module UniformContinuityTopos.Exponential
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (M   : Monoid {𝓤})
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Sheaf pt fe M
open import UniformContinuityTopos.Coverage pt fe M
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt

\end{code}

\begin{code}

module DefnOfExponential (𝒸ℴ𝓋 : Coverage 𝓦) where

 open DefnOfSheaf 𝒸ℴ𝓋

\end{code}

\begin{code}

 Exp : 𝓤  ̇ → hSet 𝓤 → hSet 𝓤
 Exp Q (P , σ) = (Q × ⟪ M ⟫ → P) , σ₃
  where
   σ₃ : is-set (Q × ⟪ M ⟫ → P)
   σ₃ = Π-is-set fe λ _ → σ

 _^^_ : Sheaf → Sheaf → Sheaf
 𝒬@(((Q , _) , _) , ♠₂) ^^ 𝒫@(((P , σ) , (_·₁_ , _)) , ♠₁) =
  ({!𝒬 , M 𝒫!} , {!!} , {!!}) , {!!}
   where
    -- _·⃗_ : underlying-set (Exp Q (P , σ)) → ⟪ M ⟫ → underlying-set (Exp Q (P , σ))
    -- ϑ ·⃗ u = λ { (q , v) → ϑ (q , u * v) }

    -- † : is-[ M ]-action (pr₂ (Exp Q (P , σ))) _·⃗_ holds
    -- † = β , γ
    --  where
    --   β : (ϑ : Q × ⟪ M ⟫ → P) → ϑ ·⃗ ε[ M ] ＝ ϑ
    --   β ϑ = dfunext fe β₁
    --    where
    --     β₁ : ϑ ·⃗ ε[ M ] ∼ ϑ
    --     β₁ (q , v) =
    --      (ϑ ·⃗ ε[ M ]) (q , v)   ＝⟨ refl                      ⟩
    --      ϑ (q , ε[ M ] * v)     ＝⟨ ap (λ - → ϑ (q , -)) (ε[ M ]-is-left-unit v) ⟩
    --      ϑ (q , v)              ∎

      -- γ : (ϑ : Q × ⟪ M ⟫ → P) (u v : ⟪ M ⟫) → ϑ ·⃗ (u * v) ＝ (ϑ ·⃗ u) ·⃗ v
      -- γ ϑ u v = dfunext fe γ₁
      --  where
      --   γ₁ : ϑ ·⃗ (u * v) ∼ (ϑ ·⃗ u) ·⃗ v
      --   γ₁ (q , v′) = (ϑ ·⃗ (u * v)) (q , v′) ＝⟨ refl ⟩
      --                 ϑ (q , (u * v) * v′)   ＝⟨ ※    ⟩
      --                 ϑ (q , u * (v * v′))   ＝⟨ refl ⟩
      --                 ((ϑ ·⃗ u) ·⃗ v) (q , v′) ∎
      --                  where
      --                   ※ = ap (λ - → ϑ (q , -)) (*[ M ]-is-associative u v v′)

    -- ♠ : is-sheaf (Exp Q (P , σ) , _·⃗_ , †) holds
    -- ♠ i 𝒻 = (ϑ , λ j → dfunext fe (φ j)) , {!!}
    --  where
    --   ϑ : Q × ⟪ M ⟫ → P
    --   ϑ (q , u) = pr₁ (pr₁ (♠₁ i λ j → 𝒻 j (q , u)))

    --   φ : (j : index (𝒥 [ i ])) → ϑ ·⃗ (𝒥 [ i ] [ j ]) ∼ 𝒻 j
    --   φ s (q , u) =
    --    (ϑ ·⃗ ((𝒥 [ i ]) [ s ])) (q , u)    ＝⟨ refl ⟩
    --    ϑ (q , (𝒥 [ i ] [ s ]) * u)        ＝⟨ {!!} ⟩
    --    {!!}                               ＝⟨ {!!} ⟩
    --    ϑ (q , u) ·₁ (𝒥 [ i ] [ s ])       ＝⟨ ψ ⟩
    --    𝒻 s (q , u)                        ∎
    --     where
    --      ψ : (ϑ (q , u) ·₁ (𝒥 [ i ] [ s ])) ＝ 𝒻 s (q , u)
    --      ψ = pr₂ (pr₁ (♠₁ i λ j → 𝒻 j (q , u))) s

\end{code}
