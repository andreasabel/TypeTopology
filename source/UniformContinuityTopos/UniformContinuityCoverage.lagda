\begin{code}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import MLTT.Fin

module UniformContinuityTopos.UniformContinuityCoverage
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators

open AllCombinators pt fe

open import UniformContinuityTopos.UniformContinuityMonoid pt fe
open import UniformContinuityTopos.MonoidAction fe
open import UniformContinuityTopos.Vector

open import UniformContinuityTopos.Coverage pt fe ℂ

open PropositionalTruncation pt

\end{code}

\begin{code}

private
 variable
  n : ℕ

cons-bit : 𝟚 → Cantor → Cantor
cons-bit b α zero     = b
cons-bit b α (succ i) = α i

cons : Vec 𝟚 n → Cantor → Cantor
cons []      = id
cons (b ∷ b⃗) = cons-bit b ∘ cons b⃗

cons-bit-is-uniformly-continuous : (b : 𝟚)
                                 → is-uniformly-continuous (cons-bit b) holds
cons-bit-is-uniformly-continuous b zero     = ∣ zero , (λ _ _ _ → ⋆) ∣
cons-bit-is-uniformly-continuous b (succ m) = ∣ m    , φ             ∣
 where
  φ : (α β : Cantor)
    → (α ＝⟦ m ⟧ β ⇒ cons-bit b α ＝⟦ succ m ⟧ cons-bit b β) holds
  φ α β p = refl , p

cons-uniformly-continuous : (b⃗ : Vec 𝟚 n) → is-uniformly-continuous (cons b⃗) holds
cons-uniformly-continuous []      = id-is-uniformly-continuous
cons-uniformly-continuous (b ∷ b⃗) =
 ∘-is-uniformly-continuous (cons b⃗) (cons-bit b) ℐℋ †
  where
   ℐℋ : is-uniformly-continuous (cons b⃗) holds
   ℐℋ = cons-uniformly-continuous b⃗

   † : is-uniformly-continuous (cons-bit b) holds
   † = cons-bit-is-uniformly-continuous b

𝔠𝔬𝔫𝔰 : Vec 𝟚 n → UC-Endomap
𝔠𝔬𝔫𝔰 b⃗ = cons b⃗ , cons-uniformly-continuous b⃗

𝒥 : Fam 𝓤₀ (Fam 𝓤₀ ⟪ ℂ ⟫)
𝒥 = ℕ , (λ n → Vec 𝟚 n , 𝔠𝔬𝔫𝔰)

open EqualityCombinator ⟪ ℂ ⟫ (monoid-carrier-is-set ℂ)

＝⟦⟧-lemma : {n : ℕ} (s : Vec 𝟚 n) (α β : Cantor) → (cons s α ＝⟦ n ⟧ cons s β) holds
＝⟦⟧-lemma []      α β = ⋆
＝⟦⟧-lemma (b ∷ s) α β = refl , ＝⟦⟧-lemma s α β

take-＝-lemma : (n : ℕ) (α β : Cantor)
              → (α ＝⟦ n ⟧ β) holds → take n α ＝ take n β
take-＝-lemma zero     α β _       = refl
take-＝-lemma (succ n) α β (p , q) =
 take (succ n) α       ＝⟨ refl ⟩
 α 0 ∷ take n (tail α) ＝⟨ †    ⟩
 β 0 ∷ take n (tail α) ＝⟨ ‡    ⟩
 β 0 ∷ take n (tail β) ＝⟨ refl ⟩
 take (succ n) β       ∎
  where
   † = ap (λ - → - ∷ take n (tail α)) p
   ‡ = ap (λ - → β 0 ∷ -) (take-＝-lemma n (tail α) (tail β) q)

＝-take-lemma : (n : ℕ) (α β : Cantor)
              → take n α ＝ take n β → (α ＝⟦ n ⟧ β) holds
＝-take-lemma zero     α β p = ⋆
＝-take-lemma (succ n) α β p = † , ‡
 where
  foo : α 0 ∷ take n (tail α) ＝ β 0 ∷ take n (tail β)
  foo = p

  † : α 0 ＝ β 0
  † = ∷-eq-lemma₁ foo

  ※ : take n (tail α) ＝ take n (tail β)
  ※ = ∷-eq-lemma₂ foo

  ‡ : (tail α ＝⟦ n ⟧ tail β) holds
  ‡ = ＝-take-lemma n (tail α) (tail β) ※

cons-bit-tail-lemma : (α : Cantor) → cons-bit (α 0) (tail α) ＝ α
cons-bit-tail-lemma α = dfunext fe (λ { zero → refl ; (succ _) → refl })

take-drop-lemma : (n : ℕ) (α : Cantor) → cons (take n α) (drop n α) ＝ α
take-drop-lemma zero     α = refl
take-drop-lemma (succ n) α =
 cons (take (succ n) α)                 (drop (succ n) α)   ＝⟨ refl  ⟩
 cons (take (succ n) α)                 (drop n (tail α))   ＝⟨ refl  ⟩
 cons (α 0 ∷ take n (tail α))           (drop n (tail α))   ＝⟨ refl  ⟩
 cons-bit (α 0) (cons (take n (tail α)) (drop n (tail α)))  ＝⟨ †     ⟩
 cons-bit (α 0) (tail α)                                    ＝⟨ ‡     ⟩
 α                                                          ∎
  where
   ℐℋ = take-drop-lemma n (tail α)
   †  = ap (cons-bit (α 0)) ℐℋ
   ‡  = cons-bit-tail-lemma α

𝒥-is-coverage : is-coverage 𝒥 holds
𝒥-is-coverage = †
 where
  Ψ : Ω 𝓤₀
  Ψ = Ɐ t ∶ ⟪ ℂ ⟫ , Ɐ m ∶ ℕ ,
       Ǝ̃ n ∶ ℕ ,
        Ɐ s ∶ Vec 𝟚 n ,
         Ǝ̃ t′ ∶ ⟪ ℂ ⟫ , Ǝ̃ s′ ∶ Vec 𝟚 m ,
          t ⊚ 𝔠𝔬𝔫𝔰 s ＝ₛ 𝔠𝔬𝔫𝔰 s′ ⊚ t′

  † : Ψ holds
  † 𝓉@(t , ζ) m = ∥∥-rec ∃-is-prop γ (ζ m)
   where
    γ : Σ n₀ ꞉ ℕ , (Ɐ α , Ɐ β , α ＝⟦ n₀ ⟧ β ⇒ t α ＝⟦ m ⟧ t β) holds
      → (Ǝ̃ n ∶ ℕ , Ɐ s ∶ Vec 𝟚 n ,
          Ǝ̃ 𝓉′ ∶ ⟪ ℂ ⟫ , Ǝ̃ s′ ∶ Vec 𝟚 m , 𝓉 ⊚ 𝔠𝔬𝔫𝔰 s ＝ₛ 𝔠𝔬𝔫𝔰 s′ ⊚ 𝓉′) holds
    γ (n₀ , ϡ) = ∣ n₀ , ♠ ∣
     where
      ♠ : (s : Vec 𝟚 n₀)
        → (Ǝ̃ 𝓉′ ∶ ⟪ ℂ ⟫ , Ǝ̃ s′ ∶ Vec 𝟚 m , 𝓉 ⊚ 𝔠𝔬𝔫𝔰 s ＝ₛ 𝔠𝔬𝔫𝔰 s′ ⊚ 𝓉′) holds
      ♠ s = ∣ 𝔡𝔯𝔬𝔭 m ⊚ 𝓉 ⊚ 𝔠𝔬𝔫𝔰 s , ∣ s′ , ※ ∣ ∣
       where
        s′ : Vec 𝟚 m
        s′ = take m (t (cons s (λ _ → ₀)))

        ॐ : (α : Cantor) → t (cons s α) ＝ cons s′ (drop m (t (cons s α)))
        ॐ α =
         t (cons s α)                                                  ＝⟨ I    ⟩
         cons (take m (t (cons s α))) (drop m (t (cons s α)))          ＝⟨ II   ⟩
         cons (take m (t (cons s (λ _ → ₀)))) (drop m (t (cons s α)))  ＝⟨ refl ⟩
         cons s′ (drop m (t (cons s α)))                               ∎
         where
          eq : (t (cons s (λ _ → ₀)) ＝⟦ m ⟧ t (cons s α)) holds
          eq = ϡ (cons s (λ _ → ₀)) (cons s α) (＝⟦⟧-lemma s (λ _ → ₀) α)

          eq′ : s′ ＝ take m (t (cons s α))
          eq′ = take-＝-lemma m (t (cons s (λ _ → ₀))) (t (cons s α)) eq

          I  = take-drop-lemma m (t (cons s α)) ⁻¹
          II = ap (λ - → cons - (drop m (t (cons s α)))) (eq′ ⁻¹)

        ※ : (𝓉 ⊚ 𝔠𝔬𝔫𝔰 s ＝ₛ 𝔠𝔬𝔫𝔰 s′ ⊚ (𝔡𝔯𝔬𝔭 m ⊚ 𝓉 ⊚ 𝔠𝔬𝔫𝔰 s)) holds
        ※ = UC-Endomap-extensional-equality ॐ

UC-coverage : Coverage 𝓤₀
UC-coverage = 𝒥 , 𝒥-is-coverage

\end{code}
