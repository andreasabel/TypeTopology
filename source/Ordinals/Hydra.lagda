Ayberk Tosun, started on the 3rd of July 2023.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt
open import MLTT.Spartan
open import MLTT.Vector
open import MLTT.Fin
open import MLTT.Bool

module Ordinals.Hydra (fe : FunExt) where

\end{code}

The type of Hydra's heads is defined inductively: it is either a singleton head
or a branch consisting of a finite and nonzero number of subheads.

\begin{code}

data HeadTree : 𝓤₀  ̇ where
 Head   : HeadTree
 Branch : (n : ℕ) → (Fin (succ n) → HeadTree) → HeadTree

\end{code}

Hydra is then just a list of heads:

\begin{code}

Hydra : ℕ → 𝓤₀  ̇
Hydra n = Fin n → HeadTree

\end{code}

\begin{code}

num-heads : {n : ℕ} → Hydra n → ℕ
num-heads {n} _ = n

\end{code}

The type of locations for heads.

\begin{code}

HeadLocation₀ : HeadTree → 𝓤₀  ̇
HeadLocation₀ Head         = 𝟙
HeadLocation₀ (Branch n φ) = Σ i ꞉ Fin (succ n) , HeadLocation₀ (φ i)

HeadLocation : {n : ℕ} → Hydra n → 𝓤₀  ̇
HeadLocation {n = n} h = Σ i ꞉ Fin n , HeadLocation₀ (h i)

\end{code}

\begin{code}

tl : {A : 𝓤  ̇} {n : ℕ} → (Fin (succ n) → A) → Fin n → A
tl f = f ∘ suc

cons : {A : 𝓤  ̇} {n : ℕ} → A → (Fin n → A) → Fin (succ n) → A
cons x φ 𝟎       = x
cons x φ (suc i) = φ i

delete : {A : 𝓤  ̇} {n : ℕ} → Fin (succ n) → (Fin (succ n) → A) → Fin n → A
delete {A = A} {zero}   i       f ()
delete {A = A} {succ n} 𝟎       f = tl f
delete {A = A} {succ n} (suc i) f = cons (f (suc i)) (delete i (tl f))

num-heads-after-cut : {n : ℕ} (h : Hydra (succ n)) → HeadLocation h → ℕ
num-heads-after-cut {n} h (i , pr₄) with h i
num-heads-after-cut {n} h (i , pr₄) | Head = n
num-heads-after-cut {n} h (i , pr₄) | Branch _ _ = succ n

\end{code}

Given a head tree and a location on it, return the head tree without that head
(no duplication is done at this point).

\begin{code}

cutₕ : (h : HeadTree) → HeadLocation₀ h → HeadTree

\end{code}

It is not possible to cut a leaf.

\begin{code}

𝔥 : {n : ℕ} → (HeadTree → HeadTree) → (Fin (succ n) → HeadTree) → Fin (succ n) → Fin (succ n) → HeadTree
𝔥 f φ k i with Fin-== i k
𝔥 f φ k i | true  = f (φ i)
𝔥 f φ k i | false = φ i

cutₕ Head ⋆ = Head

\end{code}

\begin{code}

cutₕ (Branch n        φ) (i , ns) with φ i
cutₕ (Branch zero     φ) (i , ⋆)  | Head       = Head
cutₕ (Branch (succ n) φ) (i , ⋆)  | Head       = Branch n (delete i φ)
cutₕ (Branch zero     φ) (i , is) | Branch k ψ = Branch zero {!!}
cutₕ (Branch (succ n) φ) (i , is) | Branch k ψ = {!!}

\end{code}

-- cut : {n : ℕ} (h : Hydra (succ n)) → (l : HeadLocation h) → Hydra (num-heads-after-cut h l)
-- cut h (i , is) with h i
-- cut h (i , ⋆)  | Head = delete i h
-- cut h (i , is) | Branch n φ = {!!}

\end{code}

cut-root : {n : ℕ} → Fin (succ n) → (h : Fin (succ n) → HeadTree) → Fin n → HeadTree
cut-root i h = delete i h

_▷_ : Hydra → Hydra → 𝓤₀  ̇
h₁ ▷ h₂ = {!!}

\end{code}
