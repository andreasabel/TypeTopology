\begin{code}

open import MLTT.Spartan

module UniformContinuityTopos.Vector where

\end{code}

\begin{code}

infixr 5 _∷_

data Vec (A : 𝓤  ̇) : ℕ → 𝓤  ̇ where
 []  : Vec A 0
 _∷_ : {n : ℕ} (x : A) → (xs : Vec A n) → Vec A (succ n)

\end{code}
