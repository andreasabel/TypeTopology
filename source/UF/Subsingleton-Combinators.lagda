Ayberk Tosun, 10 March 2021.

Based in part by the `Cubical.Functions.Logic` module UF.of
`agda/cubical`.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF.Subsingleton-Combinators where

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons-FunExt

\end{code}

\section{Conjunction}

\begin{code}

module Conjunction where

 _∧_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ∧ Q = (P holds × Q holds) , γ
  where
   γ = ×-is-prop (holds-is-prop P) (holds-is-prop Q)

 infixr 4 _∧_

\end{code}

\section{Universal quantification}

\begin{code}

module Universal (fe : Fun-Ext) where

 ∀[∶]-syntax : (I : 𝓤 ̇) → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∀[∶]-syntax I P = ((i : I) → P i holds) , γ
  where
   γ : is-prop ((i : I) → P i holds)
   γ = Π-is-prop fe (holds-is-prop ∘ P)


 ∀[]-syntax : {I : 𝓤 ̇} → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∀[]-syntax {I = I} P = ∀[∶]-syntax I P

 infixr -1 ∀[∶]-syntax
 infixr -1 ∀[]-syntax

 syntax ∀[∶]-syntax I (λ i → e) = Ɐ i ∶ I , e
 syntax ∀[]-syntax    (λ i → e) = Ɐ i , e

\end{code}

\section{Implication}

\begin{code}

module Implication (fe : Fun-Ext) where

 open Universal fe

 infixr 3 _⇒_

 _⇒_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ⇒ Q = (P holds → Q holds) , γ
  where
   γ : is-prop (P holds → Q holds)
   γ = Π-is-prop fe λ _ → holds-is-prop Q

 open Conjunction

 _↔_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ↔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

 infixr 3 _↔_

\end{code}

\section{Disjunction}

\begin{code}

module Disjunction (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt

 _∨_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ∨ Q = ∥ P holds + Q holds ∥ , ∥∥-is-prop

 infix 3 _∨_

\end{code}

\section{Truncation}

\begin{code}
module Truncation (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt

  ∥_∥Ω : 𝓤 ̇  → Ω 𝓤
  ∥ A ∥Ω = ∥ A ∥ , ∥∥-is-prop
\end{code}

\section{Existential quantification}

We have two versions of the existential proposition combinator: (1) `Ǝ` that
doesn't require the type family in consideration to consist of propositions, and
(2) `Ǝ̃` which works just on families of propositions. The latter is convenient
to avoid `_holds` if the family being quantified over is already propositional.

\begin{code}

module Existential (pt : propositional-truncations-exist) (fe : Fun-Ext) where

 open Truncation pt

 ∃[∶]-syntax : (I : 𝓤 ̇) → (I → 𝓥 ̇) → Ω (𝓤 ⊔ 𝓥)
 ∃[∶]-syntax I A = ∥ Σ i ꞉ I , A i ∥Ω

 ∃[]-syntax : {I : 𝓤 ̇} → (I → 𝓥 ̇) → Ω (𝓤 ⊔ 𝓥)
 ∃[]-syntax {I = I} P = ∃[∶]-syntax I P

 infixr -1 ∃[∶]-syntax
 infixr -1 ∃[]-syntax

 syntax ∃[∶]-syntax I (λ i → e) = Ǝ i ∶ I , e
 syntax ∃[]-syntax    (λ i → e) = Ǝ i , e

\end{code}

\begin{code}

 ∃̃[∶]-syntax : (I : 𝓤 ̇) → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∃̃[∶]-syntax I P = ∥ Σ i ꞉ I , P i holds ∥Ω

 ∃̃[]-syntax : {I : 𝓤 ̇} → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∃̃[]-syntax {I = I} P = ∃̃[∶]-syntax I P

 infixr -1 ∃̃[∶]-syntax
 infixr -1 ∃̃[]-syntax

 syntax ∃̃[∶]-syntax I (λ i → e) = Ǝ̃ i ∶ I , e
 syntax ∃̃[]-syntax    (λ i → e) = Ǝ̃ i , e

\end{code}

\begin{code}

 ∃![∶]-syntax : (I : 𝓤  ̇) → (I → Ω 𝓥) →  Ω (𝓤 ⊔ 𝓥)
 ∃![∶]-syntax I P = is-contr (Σ i ꞉ I , P i holds) , †
  where
   † : is-prop (is-contr (Σ i ꞉ I , P i holds))
   † = being-singleton-is-prop fe

 ∃![]-syntax : {I : 𝓤 ̇} → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∃![]-syntax {I = I} P = ∃![∶]-syntax I P

 infixr -1 ∃![∶]-syntax
 infixr -1 ∃![]-syntax

 syntax ∃![∶]-syntax I (λ i → e) = !∃ i ∶ I , e
 syntax ∃![]-syntax    (λ i → e) = !∃ i , e

\end{code}

A convenient shorthand for the identity type of a set.

\begin{code}

module EqualityCombinator (A : 𝓤  ̇) (s : is-set A) where

 infix 10 _＝ₛ_

 _＝ₛ_ : A → A → Ω 𝓤
 x ＝ₛ y = (x ＝ y) , s

\end{code}

\section{A module for importing all combinators}

\begin{code}

module AllCombinators
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

 open Conjunction       public
 open Universal   fe    public
 open Implication fe    public
 open Disjunction pt    public
 open Existential pt fe public
 open Truncation  pt    public

\end{code}
