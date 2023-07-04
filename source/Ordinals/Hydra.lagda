Ayberk Tosun, started on the 3rd of July 2023.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt
open import MLTT.Spartan
open import MLTT.Vector
open import MLTT.Fin
open import MLTT.Bool
open import Naturals.Order

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

Hydra : 𝓤₀  ̇
Hydra = Σ n ꞉ ℕ , (Fin n → HeadTree)

example₁ : Hydra
example₁ = 1 , λ { 𝟎 → Branch 0 λ { 𝟎 → Head } }

example₂ : Hydra
example₂ = 2 , (λ { 𝟎 → Head ; 𝟏 → Head })

\end{code}

\begin{code}

num-heads : Hydra → ℕ
num-heads (n , _) = n

\end{code}

The type of locations for heads.

\begin{code}

HeadLocation₀ : HeadTree → 𝓤₀  ̇
HeadLocation₀ Head         = 𝟙
HeadLocation₀ (Branch n φ) = Σ i ꞉ Fin (succ n) , HeadLocation₀ (φ i)

HeadLocation : Hydra → 𝓤₀  ̇
HeadLocation (n , h) = Σ i ꞉ Fin n , HeadLocation₀ (h i)

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

num-heads-after-cut : (h : Hydra) → HeadLocation h → ℕ
num-heads-after-cut (n , h) (i , pr₄) with h i
num-heads-after-cut (n , h) (i , pr₄) | Head = n
num-heads-after-cut (n , h) (i , pr₄) | Branch _ _ = succ n

\end{code}

Given a head tree and a location on it, return the head tree without that head
(no duplication is done at this point).

\begin{code}

cutₕ : (h : HeadTree) → HeadLocation₀ h → HeadTree

\end{code}

It is not possible to cut a leaf.

\begin{code}

replace-branch : {n : ℕ} → HeadTree → (Fin (succ n) → HeadTree) → Fin (succ n) → Fin (succ n) → HeadTree
replace-branch f φ k i with Fin-== i k
replace-branch f φ k i | true  = f
replace-branch f φ k i | false = φ i

cutₕ Head ⋆ = Head

\end{code}

\begin{code}

cutₕ (Branch n        φ) (i , ns) with φ i
cutₕ (Branch zero     φ) (i , ⋆)  | Head       = Head
cutₕ (Branch (succ n) φ) (i , ⋆)  | Head       = Branch n (delete i φ)
cutₕ (Branch zero     φ) (i , is) | Branch k ψ = Branch zero (replace-branch (cutₕ (Branch k ψ) is) φ 𝟎)
cutₕ (Branch (succ n) φ) (i , is) | Branch k ψ = Branch (succ n) (replace-branch (cutₕ (Branch k ψ) is) φ i)

\end{code}

\begin{code}

cut : (h : Hydra) → (l : HeadLocation h) → Hydra
cut (_      , φ) (i , is) with φ i
cut (succ n , φ) (i , ⋆)  | Head       = n , delete i φ
cut (succ n , φ) (i , is) | Branch k ψ = succ n , replace-branch (cutₕ (Branch k ψ) is) φ i

\end{code}
