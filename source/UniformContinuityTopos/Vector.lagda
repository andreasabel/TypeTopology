\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan

module UniformContinuityTopos.Vector where

\end{code}

\begin{code}

infixr 5 _∷_

data Vec (A : 𝓤  ̇) : ℕ → 𝓤  ̇ where
 []  : Vec A 0
 _∷_ : {n : ℕ} (x : A) → (xs : Vec A n) → Vec A (succ n)

∷-eq-lemma₁ : {A : 𝓤  ̇} → {n : ℕ} {x y : A} {xs ys : Vec A n} → x ∷ xs ＝ y ∷ ys → x ＝ y
∷-eq-lemma₁ refl = refl

∷-eq-lemma₂ : {A : 𝓤  ̇} → {n : ℕ} {x y : A} {xs ys : Vec A n} → x ∷ xs ＝ y ∷ ys → xs ＝ ys
∷-eq-lemma₂ refl = refl

\end{code}

\begin{code}

headv : {A : 𝓤  ̇} {n : ℕ} → Vec A (succ n) → A
headv (x ∷ _) = x

tailv : {A : 𝓤  ̇} {n : ℕ} → Vec A (succ n) → Vec A n
tailv (_ ∷ xs) = xs

headv-tailv-lemma : {A : 𝓤  ̇} {n : ℕ} → (s : Vec 𝟚 (succ n)) → s ＝ headv s ∷ tailv s
headv-tailv-lemma (x ∷ s) = refl

\end{code}
