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
