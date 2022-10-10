\begin{code}

module TypeTopology.UniformContinuity where

open import TypeTopology.CompactTypes
open import UF.ExcludedMiddle
open import MLTT.Spartan
open import UF.FunExt
open import UF.UA-FunExt

module Experiment (gc : Global-Choice 𝓤₀) (fe : Fun-Ext) where

 open import TypeTopology.CantorSearch fe

 cantor-compact : Compact Cantor
 cantor-compact = global-choice-gives-all-types-compact gc Cantor

 ℕ-compact : Compact ℕ
 ℕ-compact = global-choice-gives-all-types-compact gc ℕ

 ε-cantor : (Cantor → 𝟚) → Cantor
 ε-cantor = pr₁ (compact∙-gives-compact∙' κ)
  where
   κ : compact∙ Cantor
   κ = compact-pointed-gives-compact∙ (Compact-gives-compact cantor-compact) λ _ → ₀

 ε-cantor-is-selection : Cantor has-selection ε-cantor
 ε-cantor-is-selection = pr₂ (compact∙-gives-compact∙' κ)
  where
   κ : compact∙ Cantor
   κ = compact-pointed-gives-compact∙ (Compact-gives-compact cantor-compact) λ _ → ₀

 εℕ : (ℕ → 𝟚) → ℕ
 εℕ = pr₁ (compact∙-gives-compact∙' κ)
  where
   κ : compact∙ ℕ
   κ = compact-pointed-gives-compact∙ (Compact-gives-compact ℕ-compact) 0

 ∀C : (Cantor → 𝟚) → 𝟚
 ∀C p = p (ε-cantor p)

 ∀C-spec₁ : (p : Cantor → 𝟚) → ∀C p ＝ ₁ → (α : Cantor) → p α ＝ ₁
 ∀C-spec₁ p = ε-cantor-is-selection p

 ∀C-spec₂ : (p : Cantor → 𝟚) → ((α : Cantor) → p α ＝ ₁) → ∀C p ＝ ₁
 ∀C-spec₂ p φ = φ (ε-cantor p)

 _is-continuous-at_ : (Cantor → Cantor) → Cantor → 𝓤₀  ̇
 f is-continuous-at α =
  Π m ꞉ ℕ , Σ n ꞉ ℕ , Π β ꞉ Cantor , (α ＝⟦ n ⟧ β → f α ＝⟦ m ⟧ f β)

 is-continuous : (Cantor → Cantor) → 𝓤₀  ̇
 is-continuous f = Π α ꞉ Cantor , f is-continuous-at α

 is-uniformly-continuous : (Cantor → Cantor) → 𝓤₀  ̇
 is-uniformly-continuous f =
   Π m ꞉ ℕ , Σ n ꞉ ℕ , Π α ꞉ Cantor , Π β ꞉ Cantor , (α ＝⟦ n ⟧ β → f α ＝⟦ m ⟧ f β)

\end{code}

\begin{code}

 foo : (Cantor → Cantor) → (α β : Cantor) (m n : ℕ) → 𝓤₀  ̇
 foo f α β m n = α ＝⟦ n ⟧ β → f α ＝⟦ m ⟧ f β

 bool-eq-decidable : (b₁ b₂ : 𝟚) → decidable (b₁ ＝ b₂)
 bool-eq-decidable ₀ ₀ = inl refl
 bool-eq-decidable ₀ ₁ = inr (λ ())
 bool-eq-decidable ₁ ₀ = inr (λ ())
 bool-eq-decidable ₁ ₁ = inl refl

 upto-equality-detachable : (α β : Cantor) → detachable (λ n → α ＝⟦ n ⟧ β)
 upto-equality-detachable α β zero     = inl ⋆
 upto-equality-detachable α β (succ n) with bool-eq-decidable (α 0) (β 0)
 upto-equality-detachable α β (succ n) | inl p with upto-equality-detachable (tail α) (tail β) n
 upto-equality-detachable α β (succ n) | inl p | inl q = inl (p , q)
 upto-equality-detachable α β (succ n) | inl p | inr q = inr λ { (_ , r) →  q r }
 upto-equality-detachable α β (succ n) | inr p = inr λ { (q , _) → p q }

 χ₌ : (α β : Cantor) → ℕ → 𝟚
 χ₌ α β = pr₁ (co-characteristic-function (upto-equality-detachable α β))

 ϵ-δ-implication : (Cantor → Cantor) → Cantor → Cantor → ℕ × ℕ → 𝓤₀  ̇
 ϵ-δ-implication f α β (m , n) = α ＝⟦ m ⟧ β → f α ＝⟦ n ⟧ f β

 χ₌-sound : (α β : Cantor) (n : ℕ) → χ₌ α β n ＝ ₁ → α ＝⟦ n ⟧ β
 χ₌-sound α β n = pr₂ (pr₂ (co-characteristic-function (upto-equality-detachable α β)) n)

 χ₌-complete : (α β : Cantor) (n : ℕ) → α ＝⟦ n ⟧ β → χ₌ α β n ＝ ₁
 χ₌-complete α β n φ with upto-equality-detachable α β n
 χ₌-complete α β n φ | inl _ = refl
 χ₌-complete α β n φ | inr q = 𝟘-elim (q φ)

 _⇒_ : 𝟚 → 𝟚 → 𝟚
 ₀ ⇒ ψ = ₁
 ₁ ⇒ ψ = ψ

 ϵ-to-δ : (Cantor → Cantor) → Cantor → Cantor → ℕ → ℕ → 𝟚
 ϵ-to-δ f α β m n = χ₌ α β n ⇒ χ₌ (f α) (f β) m

 ϵ-to-δ-sound : (f : Cantor → Cantor) (α β : Cantor) (m n : ℕ)
              → ϵ-to-δ f α β m n ＝ ₁ → α ＝⟦ n ⟧ β → f α ＝⟦ m ⟧ f β
 ϵ-to-δ-sound f α β m n φ p with χ₌ α β n
 ϵ-to-δ-sound f α β m n φ p | ₀ = {!!}
 ϵ-to-δ-sound f α β m n φ p | ₁ = {!!}

 ϵ-to-δ-complete : (f : Cantor → Cantor) (α β : Cantor) (m n : ℕ)
                 → (α ＝⟦ n ⟧ β → f α ＝⟦ m ⟧ f β)
                 → ϵ-to-δ f α β m n ＝ ₁
 ϵ-to-δ-complete = {!!}

 mod-of-cont-at : (f : Cantor → Cantor)
                → is-continuous f
                → Cantor → ℕ → ℕ
 mod-of-cont-at f ζ α m = pr₁ (ζ α m)

 continuity⇒uc : (f : Cantor → Cantor)
               → is-continuous f
               → is-uniformly-continuous f
 continuity⇒uc f ζ m = n₀ , λ α β → † β α
  where
   p : Cantor → 𝟚
   p α = let
          n = mod-of-cont-at f ζ α m
         in
          ∀C λ β → ϵ-to-δ f α β m n

   α₀ : Cantor
   α₀ = ε-cantor p

   μ : Cantor → ℕ
   μ α = pr₁ (ζ α m)

   n₀ = μ α₀

   ♠ : Π β ꞉ Cantor , (α₀ ＝⟦ n₀ ⟧ β → f α₀ ＝⟦ m ⟧ f β)
   ♠ α = pr₂ (ζ α₀ m) α

   ♥ : p α₀ ＝ ₁ → (α : Cantor) → p α ＝ ₁
   ♥ = ε-cantor-is-selection p

   ♥₀ : (∀C λ β → ϵ-to-δ f α₀ β m (μ α₀)) ＝ ₁
      → (α : Cantor) → (∀C λ β → ϵ-to-δ f α β m (μ α)) ＝ ₁
   ♥₀ = ♥

   ♠₀ : ((β : Cantor) → ϵ-to-δ f α₀ β m (μ α₀) ＝ ₁)
      → (∀C λ β → ϵ-to-δ f α₀ β m (μ α₀)) ＝ ₁
   ♠₀ = ∀C-spec₂ (λ - → ϵ-to-δ f α₀ - m (μ α₀))

   ※ : p α₀ ＝ ₁
     → (α : Cantor) → (∀C λ β → ϵ-to-δ f α β m (μ α)) ＝ ₁
   ※ φ α = ∀C-spec₁ (λ - → ϵ-to-δ f α - m (μ α)) baz (ε-cantor (λ β → ϵ-to-δ f α β m (μ α)))
    where
     baz : (∀C λ β → ϵ-to-δ f α β m (μ α)) ＝ ₁
     baz = ♥ φ α

   ※₀ : ((β : Cantor) → ϵ-to-δ f α₀ β m (μ α₀) ＝ ₁)
      → (α β : Cantor) → ϵ-to-δ f α β m (μ α₀) ＝ ₁
   ※₀ φ α β = {!!}

   ◆ : (α β : Cantor) → α ＝⟦ μ α ⟧ β → f α ＝⟦ m ⟧ f β
   ◆ α β = pr₂ (ζ α m) β

   † : Π β ꞉ Cantor , Π α ꞉ Cantor , (α ＝⟦ n₀ ⟧ β → f α ＝⟦ m ⟧ f β)
   † β α p = {!!}
    where
     baz : (β′ : Cantor) → α₀ ＝⟦ μ α₀ ⟧ β′ → f α₀ ＝⟦ m ⟧ f β′
     baz β′ = ◆ α₀ β′

     baz′ : ((β : Cantor) → ϵ-to-δ f α₀ β m (μ α₀) ＝ ₁)
     baz′ β′ = ϵ-to-δ-complete f α₀ β′ m (μ α₀) (baz β′)

     quux : (α₁ β₁ : Cantor) → ϵ-to-δ f α₁ β₁ m (μ α₁) ＝ ₁
     quux = {!!}

   -- † : Π α ꞉ Cantor , Π β ꞉ Cantor , (α ＝⟦ n ⟧ β → f α ＝⟦ m ⟧ f β)
   -- † α β φ = {!!}
   --  where
   --   ‡ : (χ₌ α (ε-cantor (λ - → χ₌ α - n ⇒ χ₌ (f α) (f -) m)) n ⇒
   --          χ₌ (f α) (f (ε-cantor (λ - → χ₌ α - n ⇒ χ₌ (f α) (f -) m))) m)
   --         ＝ ₁
   --   ‡ = {!!}

   --   ♥ : ϵ-to-δ α β (f α) (f β) m n ＝ ₁
   --   ♥ = ε-cantor-is-selection (λ - → χ₌ α - n ⇒ χ₌ (f α) (f -) m) ‡ β

   -- p₂-dec : (n : ℕ) (α : Cantor) → decidable (p₂ n α)
   -- p₂-dec n α = {!ε-cantor λ β → ?!}

\end{code}
