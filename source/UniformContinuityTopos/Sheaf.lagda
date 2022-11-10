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

module UniformContinuityTopos.Sheaf
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (M   : Monoid {𝓤})
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Coverage pt fe M

open PropositionalTruncation pt

\end{code}

\begin{code}

module DefnOfSheaf (𝒸ℴ𝓋 : Coverage 𝓦) where

 𝒥             = pr₁ 𝒸ℴ𝓋
 𝒥-is-coverage = pr₂ 𝒸ℴ𝓋

 is-sheaf : [ M ]-set → Ω (𝓤 ⊔ 𝓦)
 is-sheaf ((P , s) , _·_ , ν) =
  Ɐ i ∶ index 𝒥 , Ɐ 𝒿 ∶ (index (𝒥 [ i ]) → P) ,
   !∃ p ∶ P ,
    Ɐ s ∶ index (𝒥 [ i ]) , p · (𝒥 [ i ] [ s ]) ＝ₛ 𝒿 s
     where
      open EqualityCombinator P s

 Sheaf : 𝓤 ⁺ ⊔ 𝓦  ̇
 Sheaf = Σ 𝒫 ꞉ [ M ]-set , is-sheaf 𝒫 holds

 P[_] : Sheaf → [ M ]-set
 P[ A , _ ] = A

 ¡_¡ : [ M ]-set → 𝓤  ̇
 ¡ (P , _) , _ ¡ = P

\end{code}

\begin{code}

 is-natural : (((P , _) , _) ((Q , _) , _) : [ M ]-set) → (P → Q) → Ω 𝓤
 is-natural ((P , _) , (_·₁_ , _)) ((Q , σ₂) , (_·₂_ , _)) ϕ =
  Ɐ p ∶ P , Ɐ u ∶ ⟪ M ⟫ , ϕ (p ·₁ u) ＝ₛ (ϕ p) ·₂ u
   where
    open EqualityCombinator Q σ₂ using (_＝ₛ_)

 ℋℴ𝓂 : Sheaf → Sheaf → 𝓤  ̇
 ℋℴ𝓂 (𝒫@((P , _) , _) , _) (𝒬@((Q , _) , _) , _) = Σ ϕ ꞉ (P → Q) , is-natural 𝒫 𝒬 ϕ holds

\end{code}


\end{code}

The terminal sheaf

\begin{code}

 𝟏ₛ : Sheaf
 𝟏ₛ = ((𝟙 , 𝟙-is-set) , _·_ , γ) , ♠
  where
   open EqualityCombinator 𝟙 𝟙-is-set

   _·_ : 𝟙 → ⟪ M ⟫ → 𝟙
   ⋆ · _ = ⋆

   γ : is-[ M ]-action 𝟙-is-set _·_ holds
   γ = 𝟙-is-prop ⋆ , λ { ⋆ x y → refl }

   ♠ : is-sheaf ((𝟙 , 𝟙-is-set) , _·_ , γ) holds
   ♠ i f = (⋆ , †) , λ { (⋆ , p) → to-subtype-＝ (λ { ⋆ → holds-is-prop ((Ɐ s ∶ index (𝒥 [ i ]) , ⋆ ＝ₛ ⋆)) }) refl }
    where
     † : (Ɐ s ∶ index (𝒥 [ i ]) , ⋆ ＝ₛ ⋆) holds
     † _ = refl

\end{code}
