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
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.Vector
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.UniformContinuityCoverage pt fe
open import UF.Subsingletons-FunExt
open import UF.Retracts

open PropositionalTruncation pt

\end{code}

\begin{code}

is-sheaf : [ ℂ ]-set 𝓥 → Ω 𝓥
is-sheaf ((P , s) , _·_ , ν) =
 Ɐ n ∶ ℕ , Ɐ 𝓅 ∶ (Vec 𝟚 n → P) ,
  !∃ p ∶ P ,
   Ɐ s ∶ Vec 𝟚 n , p · 𝔠𝔬𝔫𝔰 s ＝ₛ 𝓅 s
    where
     open EqualityCombinator P s

\end{code}

Alternative formulation of the sheaf condition that is easier to work with when
proving things are sheaves:

\begin{code}

is-sheaf′ : [ ℂ ]-set 𝓥 → Ω 𝓥
is-sheaf′ ((P , s) , _·_ , ν) =
 Ɐ n ∶ ℕ ,
  Ɐ 𝓅 ∶ (𝟚 → P) , !∃ p ∶ P , Ɐ b ∶ 𝟚 , p · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 b ＝ₛ 𝓅 b
   where
    open EqualityCombinator P s

\end{code}

\begin{code}

choose : {A : 𝓤  ̇} → A → A → 𝟚 → A
choose x y ₀ = x
choose x y ₁ = y

sheaf′-implies-sheaf : (𝒫 : [ ℂ ]-set 𝓥) → (is-sheaf′ 𝒫 ⇒ is-sheaf 𝒫) holds

sheaf′-implies-sheaf 𝒫@((P , σ) , _·_ , ν) φ zero     𝓅 = (𝓅 [] , †) , ‡
 where
  † : (s : Vec 𝟚 0) → 𝓅 [] · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 s
  † [] = pr₁ ν (𝓅 [])

  ‡ : is-central (Σ p ꞉ P , ((s : Vec 𝟚 zero) → p · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 s)) (𝓅 [] , †)
  ‡ (p , ψ) = to-subtype-＝ (λ _ → Π-is-prop fe λ _ → σ) ※
   where
    ※ = 𝓅 [] ＝⟨ ψ [] ⁻¹ ⟩ p · 𝔠𝔬𝔫𝔰 [] ＝⟨ pr₁ ν p ⟩ p ∎

sheaf′-implies-sheaf 𝒫@((P , σ) , _·_ , ν) φ (succ n) 𝓅 = (p , †) , c
 where
  𝓅₀ : Vec 𝟚 n → P
  𝓅₀ s = 𝓅 (₀ ∷ s)

  𝓅₁ : Vec 𝟚 n → P
  𝓅₁ s = 𝓅 (₁ ∷ s)

  ℐℋ₀ = sheaf′-implies-sheaf 𝒫 φ n 𝓅₀
  ℐℋ₁ = sheaf′-implies-sheaf 𝒫 φ n 𝓅₁

  p₀ : P
  p₀ = pr₁ (pr₁ ℐℋ₀)

  †₀ : (s : Vec 𝟚 n) → p₀ · 𝔠𝔬𝔫𝔰 s ＝ 𝓅₀ s
  †₀ = pr₂ (pr₁ ℐℋ₀)

  p₁ : P
  p₁ = pr₁ (pr₁ ℐℋ₁)

  †₁ : (s : Vec 𝟚 n) → p₁ · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 (₁ ∷ s)
  †₁ = pr₂ (pr₁ ℐℋ₁)

  c₀ : is-central (Σ p′ ꞉ P , ((s : Vec 𝟚 n) → p′ · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 (₀ ∷ s))) (p₀ , †₀)
  c₀ = pr₂ ℐℋ₀

  c₁ : is-central (Σ p′ ꞉ P , ((s : Vec 𝟚 n) → p′ · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 (₁ ∷ s))) (p₁ , †₁)
  c₁ = pr₂ ℐℋ₁

  p : P
  p = pr₁ (pr₁ (φ n (choose p₀ p₁)))

  † : (s : Vec 𝟚 (succ n)) → p · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 s
  † (₀ ∷ s) = p · 𝔠𝔬𝔫𝔰 (₀ ∷ s)           ＝⟨ refl ⟩
              p · (𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₀ ⊚ 𝔠𝔬𝔫𝔰 s)  ＝⟨ Ⅰ    ⟩
              (p · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₀) · 𝔠𝔬𝔫𝔰 s  ＝⟨ Ⅱ    ⟩
              (choose p₀ p₁ ₀ · 𝔠𝔬𝔫𝔰 s)  ＝⟨ Ⅲ    ⟩
              𝓅 (₀ ∷ s)                  ∎
               where
                Ⅰ = pr₂ ν p (𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₀) (𝔠𝔬𝔫𝔰 s)
                Ⅱ = ap (λ - → - · 𝔠𝔬𝔫𝔰 s) (pr₂ (pr₁ (φ n (choose p₀ p₁))) ₀)
                Ⅲ = pr₂ (pr₁ ℐℋ₀) s

  † (₁ ∷ s) = p · 𝔠𝔬𝔫𝔰 (₁ ∷ s)            ＝⟨ Ⅰ    ⟩
              (p · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₁) · 𝔠𝔬𝔫𝔰 s   ＝⟨ Ⅱ    ⟩
              choose p₀ p₁ ₁ · 𝔠𝔬𝔫𝔰 s     ＝⟨ Ⅲ    ⟩
              𝓅 (₁ ∷ s)                   ∎
               where
                Ⅰ = pr₂ ν p (𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₁) (𝔠𝔬𝔫𝔰 s)
                Ⅱ = ap (λ - → - · 𝔠𝔬𝔫𝔰 s) (pr₂ (pr₁ (φ n (choose p₀ p₁))) ₁)
                Ⅲ = pr₂ (pr₁ ℐℋ₁) s

  ‡ : is-central
       (Σ p′ ꞉ P , ((b : 𝟚) → p′ · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 b ＝ choose p₀ p₁ b))
       (p , pr₂ (pr₁ (φ n (choose p₀ p₁))))
  ‡ = pr₂ (φ n (choose p₀ p₁))

  c : is-central (Σ p′ ꞉ P , ((s : Vec 𝟚 (succ n)) → p′ · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 s)) (p , †)
  c (p′ , †′) = to-subtype-＝ (λ _ → Π-is-prop fe λ _ → σ) ♠
   where
    ♥ : (b : 𝟚) → p′ · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 b ＝ choose p₀ p₁ b
    ♥ ₀ = pr₁ (from-Σ-＝ (c₀ (p′ · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₀ , ♣))) ⁻¹
           where
            ♣ : (s : Vec 𝟚 n) → (p′ · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₀) · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 (₀ ∷ s)
            ♣ s = (p′ · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₀) · 𝔠𝔬𝔫𝔰 s     ＝⟨ Ⅰ          ⟩
                  p′ · (𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₀ ⊚ 𝔠𝔬𝔫𝔰 s)     ＝⟨ refl       ⟩
                  p′ · 𝔠𝔬𝔫𝔰 (₀ ∷ s)              ＝⟨ †′ (₀ ∷ s) ⟩
                  𝓅 (₀ ∷ s)                      ∎
                   where
                    Ⅰ = pr₂ ν p′ (𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₀) (𝔠𝔬𝔫𝔰 s) ⁻¹
    ♥ ₁ = pr₁ (from-Σ-＝ (c₁ (p′ · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₁ , ♣))) ⁻¹
           where
            ♣ : (s : Vec 𝟚 n) → (p′ · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₁) · 𝔠𝔬𝔫𝔰 s ＝ 𝓅 (₁ ∷ s)
            ♣ s = (p′ · 𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₁) · 𝔠𝔬𝔫𝔰 s     ＝⟨ Ⅰ          ⟩
                  p′ · (𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₁ ⊚ 𝔠𝔬𝔫𝔰 s)     ＝⟨ refl       ⟩
                  p′ · 𝔠𝔬𝔫𝔰 (₁ ∷ s)              ＝⟨ †′ (₁ ∷ s) ⟩
                  𝓅 (₁ ∷ s)                      ∎
                   where
                    Ⅰ = pr₂ ν p′ (𝔠𝔬𝔫𝔰-𝔟𝔦𝔱 ₁) (𝔠𝔬𝔫𝔰 s) ⁻¹

    ♠ : p ＝ p′
    ♠ = pr₁ (from-Σ-＝ (‡ (p′ , ♥)))

\end{code}

\begin{code}

Sheaf : (𝓤 : Universe) → 𝓤 ⁺  ̇
Sheaf 𝓤 = Σ 𝒫 ꞉ [ ℂ ]-set 𝓤 , is-sheaf 𝒫 holds

∣_∣ₚ : [ ℂ ]-set 𝓤 → 𝓤  ̇
∣ 𝒫 ∣ₚ = pr₁ (pr₁ 𝒫)

∣_∣ₛ : Sheaf 𝓤 → 𝓤  ̇
∣ 𝒫 ∣ₛ = pr₁ (pr₁ (pr₁ 𝒫))

\end{code}

\begin{code}

is-natural : (𝒫 𝒬 : [ ℂ ]-set 𝓤) → (∣ 𝒫 ∣ₚ → ∣ 𝒬 ∣ₚ) → Ω 𝓤
is-natural ((P , _) , (_·₁_ , _)) ((Q , σ₂) , (_·₂_ , _)) ϕ =
 Ɐ p ∶ P , Ɐ u ∶ ⟪ ℂ ⟫ , ϕ (p ·₁ u) ＝ₛ (ϕ p) ·₂ u
  where
   open EqualityCombinator Q σ₂ using (_＝ₛ_)

is-natural′ : (𝒫 𝒬 : Sheaf 𝓤) → (∣ 𝒫 ∣ₛ → ∣ 𝒬 ∣ₛ) → Ω 𝓤
is-natural′ (𝒫 , _) (𝒬 , _) = is-natural 𝒫 𝒬

ℋℴ𝓂 : Sheaf 𝓤 → Sheaf 𝓤 → 𝓤  ̇
ℋℴ𝓂 (𝒫@((P , _) , _) , _) (𝒬@((Q , _) , _) , _) =
 Σ ϕ ꞉ (P → Q) , is-natural 𝒫 𝒬 ϕ holds

apply : (𝒫 𝒬 : Sheaf 𝓤) → ℋℴ𝓂 𝒫 𝒬 → ∣ 𝒫 ∣ₛ → ∣ 𝒬 ∣ₛ
apply 𝒫 𝒬 (𝒻 , _) = 𝒻

underlying-presheaf : Sheaf 𝓤 → [ ℂ ]-set 𝓤
underlying-presheaf (P , _) = P

sheaf-is-set : (𝒫 : Sheaf 𝓤) → is-set ∣ 𝒫 ∣ₛ
sheaf-is-set (((P , σ) , _) , _) = σ

ℋℴ𝓂-is-set : (𝒫 𝒬 : Sheaf 𝓤) → is-set (ℋℴ𝓂 𝒫 𝒬)
ℋℴ𝓂-is-set 𝒫 𝒬 =
 Σ-is-set
  (Π-is-set fe λ _ → sheaf-is-set 𝒬)
  λ f → props-are-sets (holds-is-prop (is-natural′ 𝒫 𝒬 f))

ℋℴ𝓂ₛ : Sheaf 𝓤 → Sheaf 𝓤 → hSet 𝓤
ℋℴ𝓂ₛ 𝒫 𝒬 = ℋℴ𝓂 𝒫 𝒬 , ℋℴ𝓂-is-set 𝒫 𝒬

\end{code}

The identity natural transformation:

\begin{code}

𝟏[_] : (P : Sheaf 𝓤) → ℋℴ𝓂 P P
𝟏[ P ] = id , λ _ _ → refl

\end{code}

Composition of natural transformations:

\begin{code}

∘-is-natural : (𝒫 𝒬 ℛ : Sheaf 𝓤) (ϕ : ∣ 𝒫 ∣ₛ → ∣ 𝒬 ∣ₛ) (ψ : ∣ 𝒬 ∣ₛ → ∣ ℛ ∣ₛ)
             → is-natural′ 𝒫 𝒬 ϕ holds
             → is-natural′ 𝒬 ℛ ψ holds
             → is-natural′ 𝒫 ℛ (ψ ∘ ϕ) holds
∘-is-natural 𝒫 𝒬 ℛ ϕ ψ β γ p u = ψ (ϕ (p ·₁ u))     ＝⟨ ap ψ (β p u) ⟩
                                 ψ (ϕ p ·₂ u)       ＝⟨ γ (ϕ p) u    ⟩
                                 ψ (ϕ p) ·₃ u       ∎
  where
   _·₁_ = μ ℂ (underlying-presheaf 𝒫)
   _·₂_ = μ ℂ (underlying-presheaf 𝒬)
   _·₃_ = μ ℂ (underlying-presheaf ℛ)

comp : (𝒫 𝒬 ℛ : Sheaf 𝓤) → ℋℴ𝓂 𝒬 ℛ → ℋℴ𝓂 𝒫 𝒬 → ℋℴ𝓂 𝒫 ℛ
comp 𝒫 𝒬 ℛ (ψ , ν₂) (ϕ , ν₁) = (ψ ∘ ϕ) , χ
 where
  χ : is-natural′ 𝒫 ℛ (ψ ∘ ϕ) holds
  χ = ∘-is-natural 𝒫 𝒬 ℛ ϕ ψ ν₁ ν₂

\end{code}

The terminal sheaf

\begin{code}

𝟏ₛ : Sheaf 𝓤
𝟏ₛ = ((𝟙 , 𝟙-is-set) , _·_ , γ) , ♠
 where
  open EqualityCombinator 𝟙 𝟙-is-set

  _·_ : 𝟙 → ⟪ ℂ ⟫ → 𝟙
  ⋆ · _ = ⋆

  γ : is-[ ℂ ]-action 𝟙-is-set _·_ holds
  γ = 𝟙-is-prop ⋆ , λ { ⋆ x y → refl }

  ♠ : is-sheaf ((𝟙 , 𝟙-is-set) , _·_ , γ) holds
  ♠ i f = (⋆ , †) , λ { (⋆ , p) → to-subtype-＝ (λ { ⋆ → holds-is-prop ((Ɐ s ∶ Vec 𝟚 i , ⋆ ＝ₛ ⋆)) }) refl }
   where
    † : (Ɐ s ∶ Vec 𝟚 i , ⋆ ＝ₛ ⋆) holds
    † _ = refl

\end{code}

\begin{code}

 -- self-action-is-sheaf : is-sheaf (self-action M) holds
 -- self-action-is-sheaf i 𝒿 = (ε[ M ] , †) , {!!}
 --  where
 --   † : (j : index (𝒥 [ i ])) → ε[ M ] *[ M ] (𝒥 [ i ] [ j ]) ＝ 𝒿 j
 --   † j = {!!}

\end{code}
