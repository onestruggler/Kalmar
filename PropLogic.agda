-- This file comes from the agda class taught by Peter Selinger at
-- Dalhousie University. It contains a bonus question that
-- propostional logic is complete. We will show this in
-- Completeness.agda.

-- The course link:
-- https://www.mathstat.dal.ca/~selinger/agda-lectures/

{-# OPTIONS --without-K --safe #-}
module PropLogic where

-- We replace the library (lib-3.0) used in class by the stdlib v2. 

-- open import Equality
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; inspect ; [_] ; trans ; sym)

-- open import Nat
open import Data.Nat using (ℕ)

-- open import Bool
-- renaming and defining new connectives.
open import Data.Bool renaming(_∧_ to _and_ ; _∨_ to _or_) using (Bool ; not ; true ; false)
_implies_ : Bool → Bool → Bool
_implies_ a b = not a or b 


-- ----------------------------------------------------------------------
-- * Introduction

-- In this project, we will formalize boolean (i.e., classical)
-- propositional logic, define a notion of derivation for the logic,
-- give a semantics for the logic in terms of truth tables (also known
-- as boolean assignments), and prove the soundness of the derivation
-- rules.

-- ----------------------------------------------------------------------
-- * The set of boolean formulas

-- We start by defining the set of boolean formulas. Informally, the
-- formulas are given by the following grammar:
--
-- Formula   A, B ::= P n | A ∧ B | A ⇒ B | ⊥ | ⊤
--
-- Here, n is a natural number, and P n is the nth propositional
-- symbol. A ∧ B is conjunction, A ⇒ B is implication, ⊥ is "false"
-- (also known as a contradiction), and ⊤ is "true". You can type
-- these symbols in Emacs Agda mode using \and, \=>, \bot, and \top.
-- Note that the symbol "⊤" is not the same as the capital letter "T".

-- The set of propositional formulas as an Agda datatype:
data Formula : Set where
  P : ℕ -> Formula
  _∧_ : Formula -> Formula -> Formula
  _⇒_ : Formula -> Formula -> Formula
  ⊥ : Formula
  ⊤ : Formula
  ¬_ : Formula -> Formula
  _∨_ : Formula -> Formula -> Formula

infixl 9 _∧_
infixr 8 _⇒_

infix 20 ¬_

-- ----------------------------------------------------------------------
-- * Derivations

-- The most important concept in logic is that of derivability.
-- "Derivation" is another word for "proof". If A₁, ..., Aₙ, B are
-- formulas, we write
--
--       A₁, ..., Aₙ ⊢ 
--
-- for the statement "the conclusion B can be derived from hypotheses
-- A₁, ..., Aₙ". The symbol "⊢" is pronounced "entails", and we also
-- say "A₁, ..., Aₙ entails B". You can type this symbol as \|- or
-- \entails or \vdash.
-- 
-- Although entailment "⊢" is somewhat similar to implication "⇒",
-- there is an important difference: an implication A ⇒ B is a
-- formula, so it could be used, for example, as a hypothesis or as a
-- conclusion in a proof. Entailment is a statement about formulas,
-- i.e., entailment means: there exists a proof of B from hypotheses
-- A₁, ..., Aₙ. Entailment is not itself a formula; it is a statement
-- about provability. Thus, entailment is a relation between a list of
-- formulas (the hypotheses) and a formula (the conclusion).

-- ----------------------------------------------------------------------
-- ** Contexts

-- Before we can formalize entailment, we must formalize lists of
-- formulas. A list of formulas is also called a "context". We
-- write Γ for an arbitrary context.
--
-- Because a context can also be empty (a list of zero formulas), it
-- is convenient to use the empty context as the base case. Then we
-- can give the following recursive definition of contexts: a context
-- is either the empty context, or it is obtained from another context
-- by adding one more formula on the right. In other words, we have
-- the following grammar for contexts:
--
-- Context   Γ ::= Empty | Γ, A
--
-- We formalize this as the following Agda datatype:

{-
data Context : Set where
  Empty : Context
  _,_ : Context -> Formula -> Context
-}

-- Modification: We use List Formula as Context instead of defining a
-- new data type. This will ease the proof using list with distinct
-- elements.


open import Data.List using (List ; _∷_ ; [])
Context = List Formula

infixl 7 _,_

-- _,_ : Context -> Formula -> Context
-- _,_ Γ F = F ∷ Γ

pattern _,_ Γ F = F ∷ Γ
pattern Empty = []


-- We also need the membership relation for contexts. We define the
-- relation A ∈ Γ to mean "the formula A is in the context Γ". The
-- symbol ∈ is typed as \in. The membership relation can be
-- recursively defined as follows: the empty context has no members,
-- and the members of the context Γ, A are A and the members of
-- Γ. More formally, we have the following inference rules for
-- membership:
--
-- ───────────── (∈-base)
--   A ∈ Γ, A
--
--
--     A ∈ Γ
-- ───────────── (∈-step)
--   A ∈ Γ, B
--
-- An inference rule, written with a horizontal line, has the
-- following meaning: if the (zero or more) statements above the line
-- are true, then the statement below the line is true. The statements
-- above the line are called the hypotheses of the inference rule, and
-- the statement below the line is called the conclusion. The name of
-- each inference rule (e.g., ∈-base, ∈-step) is written next to the
-- rule. We use inference rules to define a relation, in this case the
-- relation "∈". By definition, "∈" is the smallest relation
-- satisfying (∈-base) and (∈-step).
--
-- We can directly translate these inference rules into Agda as
-- follows:
data _∈_ : Formula -> Context -> Set where
  ∈-base : ∀ {A : Formula} {Γ : Context} -> A ∈ (Γ , A)
  ∈-step : ∀ {A B : Formula} {Γ : Context} -> A ∈ Γ -> A ∈ (Γ , B)

infixl 6 _∈_

-- ----------------------------------------------------------------------
-- ** Entailment

-- We now define the entailment relation. Recall that the entailment
-- relation Γ ⊢ A is supposed to mean "the conclusion A can be derived
-- from the hypotheses Γ". Defining entailment therefore requires us
-- to formalize what we mean by "derived". In other words, we have to
-- give a set of proof rules for propositional logic. Let me first
-- write these proof rules in the style of inference rules. These
-- rules define the relation "⊢":
--
--    A ∈ Γ
-- ───────────── (assump)
--    Γ ⊢ A
--
--
--   Γ ⊢ A   Γ ⊢ B 
-- ───────────────── (∧-intro)
--     Γ ⊢ A ∧ B
-- 
--
--     Γ ⊢ A ∧ B
-- ───────────────── (∧-elim1)
--       Γ ⊢ A
-- 
--
--     Γ ⊢ A ∧ B
-- ───────────────── (∧-elim2)
--       Γ ⊢ B
-- 
--
--     Γ, A ⊢ B
-- ───────────────── (⇒-intro)
--     Γ ⊢ A ⇒ B
--
--
--     Γ ⊢ A ⇒ B    Γ ⊢ A
-- ────────────────────────── (⇒-elim)
--           Γ ⊢ B
--
--
--     Γ ⊢ (A ⇒ ⊥) ⇒ ⊥
-- ────────────────────── (double-negation)
--         Γ ⊢ A
--
-- 
-- ───────────────── (⊤-intro)
--      Γ ⊢ ⊤
--
-- 
-- The rule (assump) states that if A is one of the hypotheses, then A
-- can be derived from the hypothesis. Basically A is true "by assumption".
--
-- Several of the connectives, such as ∧ and ⇒, have an "introduction"
-- rule, which shows how to prove such a formula, and an "elimination"
-- rule, which shows how such a formula can be used to prove other
-- things. The rule (∧-intro) states that to prove A ∧ B from the
-- given hypotheses Γ, we must separately derive A and B. Conversely,
-- the rules (∧-elim1) and (∧-elim2) state that if we have already
-- derived A ∧ B, then we may separately conclude A and B. The rule
-- (⇒-intro) states that to prove an implication A ⇒ B, we must assume
-- A and prove B. In other words, to derive A ⇒ B from some hypotheses
-- Γ, we must prove B from the hypotheses Γ, A. The rule (⇒-elim) is
-- also known by its Latin name "modus ponens". It states that if we
-- can prove A ⇒ B and we can also prove A, then we may conclude
-- B. The rule (double-negation) is required to make the logic
-- classical.  Informally, it states that we can prove A by assuming
-- "not A" and deriving a contradiction. Remember that "not A" is an
-- abbreviation for (A ⇒ ⊥). The rule (⊤-intro) states that ⊤ can be
-- derived from any set of hypotheses.

-- We can directly translate the above rules into Agda:
data _⊢_ : Context -> Formula -> Set where
  assump : ∀ {Γ A} -> A ∈ Γ -> Γ ⊢ A
  ∧-intro : ∀ {Γ A B} -> Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ A ∧ B
  ∧-elim1 : ∀ {Γ A B} -> Γ ⊢ A ∧ B -> Γ ⊢ A 
  ∧-elim2 : ∀ {Γ A B} -> Γ ⊢ A ∧ B -> Γ ⊢ B
  ⇒-intro : ∀ {Γ A B} -> Γ , A ⊢ B -> Γ ⊢ A ⇒ B
  ⇒-elim : ∀ {Γ A B} -> Γ ⊢ A ⇒ B -> Γ ⊢ A -> Γ ⊢ B
  double-negation : ∀ {Γ A} -> Γ ⊢ (A ⇒ ⊥) ⇒ ⊥ -> Γ ⊢ A
  ⊤-intro : ∀ {Γ} -> Γ ⊢ ⊤
  ¬-intro : ∀ {Γ A} -> Γ , A ⊢ ⊥ -> Γ ⊢ ¬ A
  ¬-elim : ∀ {Γ A} -> Γ  ⊢ ¬ A -> Γ ⊢ A -> Γ ⊢ ⊥
  ∨-intro1 : ∀ {Γ A B} -> Γ ⊢ A -> Γ ⊢ A ∨ B 
  ∨-intro2 : ∀ {Γ A B} -> Γ ⊢ B  -> Γ ⊢ A ∨ B 
  ∨-elim : ∀ {Γ A B C} -> Γ ⊢ A ∨ B -> Γ , A ⊢ C -> Γ , B ⊢ C -> Γ ⊢ C

infixl 4 _⊢_

-- ----------------------------------------------------------------------
-- ** Weakening

-- "Weakening" is the property that if we add additional hypotheses to
-- an entailment (or change their order), the entailment remains valid.
-- More formally, weakening states that Γ ⊢ A and Γ ⊆ Γ' implies Γ' ⊢ A.
-- 
-- To state weakening, we must first define ⊆. The symbol ⊆ can be
-- typed as \subseteq or \seq.
_⊆_ : Context -> Context -> Set
Γ ⊆ Γ' = ∀ {A} -> A ∈ Γ -> A ∈ Γ'

infix 4 _⊆_

-- We need a lemma about ⊆:
lemma-⊆ : ∀ {Γ Γ' A} -> Γ ⊆ Γ' -> Γ , A ⊆ Γ' , A
lemma-⊆ hyp ∈-base = ∈-base
lemma-⊆ hyp (∈-step hyp2) = ∈-step (hyp hyp2)

lemma-⊆-ext : ∀ {Γ Γ' A} -> Γ ⊆ Γ' -> Γ ⊆ Γ' , A
lemma-⊆-ext hyp =  \ x -> ∈-step (hyp x)   

lemma-⊆-ext' : ∀ {Γ A} -> Γ ⊆ Γ , A
lemma-⊆-ext' = lemma-⊆-ext \ x -> x

lemma-⊆-empty : ∀ {Γ} -> Empty ⊆ Γ
lemma-⊆-empty {Γ} {A} () 


-- Prove the weakening lemma:
weakening : ∀ {Γ Γ' A} -> Γ ⊢ A -> Γ ⊆ Γ' -> Γ' ⊢ A
weakening (assump x) w = assump (w x)
weakening (∧-intro d d₁) w = ∧-intro (weakening d w) (weakening d₁ w) 
weakening (∧-elim1 d) w = ∧-elim1 (weakening d w )  
weakening (∧-elim2 d) w = ∧-elim2 (weakening d w)  
weakening (⇒-intro d) w = ⇒-intro (weakening d (lemma-⊆ w) ) 
weakening (⇒-elim d d₁) w = ⇒-elim (weakening d w ) (weakening d₁ w ) 
weakening (double-negation d) w = double-negation (weakening d w ) 
weakening ⊤-intro w = ⊤-intro 
weakening (¬-intro d) w  = ¬-intro (weakening d (lemma-⊆ w ) ) 
weakening (¬-elim d e) w  = ( ¬-elim (weakening d w) (weakening e w))  
weakening (∨-intro1 d) w  = ∨-intro1 (weakening d w) 
weakening (∨-intro2 d) w  = ∨-intro2 (weakening d w) 
weakening (∨-elim d e f) w  = ∨-elim (weakening d w) (weakening e (lemma-⊆ w)) (weakening f (lemma-⊆ w) ) 

-- ----------------------------------------------------------------------
-- ** A derived rule

-- Classical logic also has the following rule, called "ex falsum
-- quodlibet" or "⊥-elim".
--
--       Γ ⊢ ⊥
-- ───────────────── (⊥-elim)
--       Γ ⊢ A
--
-- The reason we did not include it in the proof rules in the above
-- definition of entailment it that it follows from the other rules.
-- Prove it:


⊥-elim : ∀ {Γ A} -> Γ ⊢ ⊥ -> Γ ⊢ A
⊥-elim {Γ} {A} a = double-negation a-⊥-⊥  where
  a-⊥ : Γ ⊢ A ⇒ ⊥
  a-⊥ = ⇒-intro (weakening a (lemma-⊆-ext \ x -> x ) )  
  a-⊥-⊥ : Γ ⊢ (A ⇒ ⊥) ⇒ ⊥
  a-⊥-⊥ = ⇒-intro (weakening a (lemma-⊆-ext \ x -> x ) )  

-- ----------------------------------------------------------------------
-- * Truth table semantics

-- ----------------------------------------------------------------------
-- ** Truth assignments and interpretation

-- Remember that the atomic formulas of our logic are P 0, P 1, P 2,
-- and so on. The fundamental concept of truth tables is that of a
-- "truth assignment", namely a map from atomic formulas to {T, F}.
-- We usually denote a truth assignment by the letter ρ = \rho.
--
-- We formalize truth assignments as maps from ℕ to Bool.
Assign : Set
Assign = ℕ -> Bool

-- Given a truth assignment ρ, we can compute the truth value (true or
-- false) of any given formula. This is called the "interpretation" of
-- formulas.

interp : Assign -> Formula -> Bool
interp ρ (P x) = ρ x
interp ρ (A ∧ B) = (interp ρ A) and (interp ρ B)
interp ρ (A ⇒ B) = (interp ρ A) implies (interp ρ B)
interp ρ ⊥ = false
interp ρ ⊤ = true
interp ρ (¬ A) = not (interp ρ A)
interp ρ (A ∨ B) = (interp ρ A) or (interp ρ B)


-- Lift the interp function to a list of formulas. We interpret a list
-- of formulas basically as the conjunction of the formulas, i.e., the
-- interpretation of Γ is true if and only if the interpretation of
-- all A ∈ Γ is true.
interps : Assign -> Context -> Bool
interps ρ Empty = true
interps ρ (c , x) = interps ρ c and interp ρ x  


-- ----------------------------------------------------------------------
-- ** Semantic entailment

-- We write Γ ⊧ A if under all assignments ρ, if Γ is true, then A is true.
-- A special case is when the context Γ is empty. In that case, ⊧ A means
-- that A is true under all assignments, i.e., A is a tautology.
--
-- The symbol ⊧ is pronounced "models", and you can type it as
-- \models. Please note that this is a different symbol from ⊨ = \|=.
-- We use the symbol "⊧" here.
-- 
-- The relation ⊧ is also called "semantic entailment" or "truth table
-- entailment", to distinguish it from ⊢, which is "syntactic
-- entailment" or "derivability".

-- We define semantic entailment.
-- _⊧_ : Context -> Formula -> Set
-- Γ ⊧ A = ∀ ρ -> interps ρ Γ ≡ true -> interp ρ A ≡ true

_⊧_ : Context -> Formula -> Set
Γ ⊧ f = (ρ : Assign) -> interps ρ Γ ≡ true -> interp ρ f ≡ true

infix 4 _⊧_ 

-- ----------------------------------------------------------------------
-- * Soundness

-- ----------------------------------------------------------------------
-- ** Lemmas about the boolean connectives

-- The boolean functions 'and' and 'implies' are defined in Bool.agda.
-- We need to know certain ones of their properties.

boolCases : {p : Set} -> (a : Bool) -> (a ≡ true -> p) -> (a ≡ false -> p) -> p
boolCases true t f = t refl
boolCases false t f = f refl

lemma-and-1 : {a b : Bool} -> a ≡ true -> b ≡ true -> a and b ≡ true
lemma-and-1 refl refl = refl

lemma-and-2 : {a b : Bool} -> a and b ≡ true -> a ≡ true
lemma-and-2 {true} {true} abt = refl

lemma-and-3 : {a b : Bool} -> a and b ≡ true -> b ≡ true
lemma-and-3 {true} {true} abt = refl 


lemma-imp-1 : {a b : Bool} -> a implies b ≡ true -> a ≡ true -> b ≡ true
lemma-imp-1 {true} {true} aibt at = refl

lemma-imp-2 : {a b : Bool} -> a ≡ false -> a implies b ≡ true
lemma-imp-2 {false} {true} af = refl
lemma-imp-2 {false} {false} af = refl

lemma-imp-3 : {a b : Bool} -> b ≡ true -> a implies b ≡ true
lemma-imp-3 {true} {true} bt = refl
lemma-imp-3 {false} {b} bt = refl

lemma-doubleNeg : {a : Bool} -> (a implies false) implies false ≡ true -> a ≡ true
lemma-doubleNeg {true} a-f-ft = refl


lemma-not-true : {a : Bool} -> a ≡ true -> not a ≡ false
lemma-not-true {.true} refl = refl 


lemma-not-false : {a : Bool} -> a ≡ false -> not a ≡ true
lemma-not-false {.false} refl = refl 


lemma-or-1 : {a b : Bool} -> a ≡ true -> a or b ≡ true
lemma-or-1 refl  = refl

lemma-or-2 : {a b : Bool} -> b ≡ true -> a or b ≡ true
lemma-or-2 {true} {.true} refl = refl
lemma-or-2 {false} {.true} refl = refl 

-- like boolCases
lemma-or-3 : {C : Set} ->  {a b : Bool} -> a or b ≡ true -> (a ≡ true -> C) -> (b ≡ true -> C) -> C
lemma-or-3 {a = true} {true} aob ca cb = ca aob
lemma-or-3 {a = false} {true} aob ca cb = cb aob
lemma-or-3 {a = true} {false} aob ca cb = ca refl 
 

-- ----------------------------------------------------------------------
-- ** Lemmas about the soundness of individual rules

-- Each of the proof rules of logic has a semantic counterpart.

lemma-assump : ∀ Γ A -> A ∈ Γ -> Γ ⊧ A
lemma-assump (._ , A) A ∈-base = \ ρ ct -> lemma-and-3 ct  
lemma-assump (Γ' , B) A (∈-step hyp) = \ ρ ct -> (lemma-assump Γ' A hyp) ρ (lemma-and-2 ct ) 

lemma-∧-intro : ∀ Γ A B -> Γ ⊧ A -> Γ ⊧ B -> Γ ⊧ A ∧ B
lemma-∧-intro Γ A B as bs = \ ρ ct -> lemma-and-1 (as ρ ct ) (bs ρ ct )  

lemma-∧-elim1 : ∀ Γ A B -> Γ ⊧ A ∧ B -> Γ ⊧ A
lemma-∧-elim1 Γ A B abs = \ ρ ct -> lemma-and-2 (abs ρ ct)

lemma-∧-elim2 : ∀ Γ A B -> Γ ⊧ A ∧ B -> Γ ⊧ B
lemma-∧-elim2 Γ A B abs = \ ρ ct -> lemma-and-3 (abs ρ ct)


lemma-⇒-intro' : ∀ Γ A B -> Γ , A ⊧ B -> Γ ⊧ A ⇒ B
lemma-⇒-intro' Γ A B a-bs ρ ct  = boolCases (interp ρ A) (\ x -> lemma-imp-3 (a-bs ρ (lemma-and-1 ct x ) ) ) \ x -> lemma-imp-2 x   

lemma-⇒-intro : ∀ Γ A B -> Γ , A ⊧ B -> Γ ⊧ A ⇒ B
lemma-⇒-intro Γ A B a-bs ρ ct with (interp ρ) A | inspect (interp ρ) A
lemma-⇒-intro Γ A B a-bs ρ ct | true | [ eq ] = lemma-imp-3 (a-bs ρ (lemma-and-1 ct eq ) )
lemma-⇒-intro Γ A B a-bs ρ ct | false | [ eq ] = refl 


lemma-⇒-elim : ∀ Γ A B -> Γ ⊧ A ⇒ B -> Γ ⊧ A -> Γ ⊧ B
lemma-⇒-elim Γ A B a-bs as = \ ρ ct -> lemma-imp-1 (a-bs ρ ct ) (as ρ ct )  

lemma-double-negation : ∀ Γ A -> Γ ⊧ (A ⇒ ⊥) ⇒ ⊥ -> Γ ⊧ A
lemma-double-negation Γ A anns = \ ρ ct -> lemma-doubleNeg (anns ρ ct )  

lemma-⊤-intro : ∀ Γ -> Γ ⊧ ⊤
lemma-⊤-intro Γ = \ ρ ct -> refl 


lemma-¬-intro : ∀ Γ A -> Γ , A ⊧ ⊥ -> Γ ⊧ ¬ A
lemma-¬-intro Γ A a ρ ct with (interp ρ) A | inspect (interp ρ) A
lemma-¬-intro Γ A a ρ ct | true  | [ eq ] = a ρ (lemma-and-1 ct eq)
lemma-¬-intro Γ A a ρ ct | false | [ eq ] = refl 

lemma-¬-intro' : ∀ Γ A -> Γ , A ⊧ ⊥ -> Γ ⊧ ¬ A
lemma-¬-intro' Γ A a ρ ct = boolCases (interp ρ A) (\x -> trans (lemma-not-true x ) (a ρ (lemma-and-1 ct x ) )  ) \ x -> lemma-not-false x   


lemma-¬-elim : ∀ Γ A -> Γ ⊧ ¬ A -> Γ ⊧  A -> Γ ⊧ ⊥
lemma-¬-elim Γ A a b ρ ct = boolCases (interp ρ A) (\ x -> trans (sym (lemma-not-true x)) (a ρ ct )   ) \ x -> trans (sym  x ) (b ρ ct)  


lemma-∨-intro1 : ∀ Γ A B -> Γ ⊧  A -> Γ ⊧  A ∨ B
lemma-∨-intro1 Γ A B a ρ ct = lemma-or-1 (a ρ ct )


lemma-∨-intro2 : ∀ Γ A B -> Γ ⊧  B -> Γ ⊧  A ∨ B
lemma-∨-intro2 Γ A B a ρ ct = lemma-or-2 (a ρ ct )


lemma-∨-elim : ∀ Γ A B C -> Γ ⊧  A ∨ B -> Γ , A ⊧  C -> Γ , B ⊧  C -> Γ ⊧ C   
lemma-∨-elim Γ A B C aob ac bc ρ ct = lemma-or-3 (aob ρ ct) (\ x -> ac ρ (lemma-and-1 ct x )  ) \ x -> bc ρ (lemma-and-1 ct x )    


-- ----------------------------------------------------------------------
-- * The soundness theorem of boolean logic.

-- Soundness states that Γ ⊢ A implies Γ ⊧ A, or equivalently:
-- everything that is provable is valid.

-- 4. Prove the soundness of boolean logic. 
sound : ∀ Γ A -> Γ ⊢ A -> Γ ⊧ A
sound Γ A (assump x) = lemma-assump Γ A x 
sound Γ (A ∧ B) (∧-intro hyp hyp₁) = lemma-∧-intro Γ A B (sound Γ A hyp) (sound Γ B hyp₁)
sound Γ A (∧-elim1 {B = B} hyp) = lemma-∧-elim1 Γ A B (sound Γ  (A ∧ B) hyp ) 
sound Γ A (∧-elim2 {A = A₁} hyp) = lemma-∧-elim2 Γ  A₁ A ((sound Γ  (A₁ ∧ A) hyp ) ) 
sound Γ (A ⇒ B) (⇒-intro hyp) = lemma-⇒-intro Γ A B (sound (Γ , A) B   hyp ) 
sound Γ A (⇒-elim {A = A₁} hyp hyp₁) = lemma-⇒-elim Γ A₁ A (sound Γ (A₁ ⇒ A) hyp ) (sound Γ A₁ hyp₁)  
sound Γ A (double-negation hyp) = lemma-double-negation Γ A (sound Γ ((A ⇒ ⊥) ⇒ ⊥) hyp) 
sound Γ .⊤ ⊤-intro = λ ρ _ → refl
sound Γ (¬ A) (¬-intro x) = lemma-¬-intro' Γ  A ((sound (Γ , A) ⊥  x ) )
sound Γ .⊥ (¬-elim {A = A} x y) = lemma-¬-elim Γ A (sound Γ (¬ A) x) (sound Γ  A y)  
sound Γ (A ∨ B) (∨-intro1 x) = lemma-∨-intro1 Γ A B (sound Γ A x ) 
sound Γ (A ∨ B) (∨-intro2 x) = lemma-∨-intro2 Γ A B (sound Γ B x ) 
sound Γ C (∨-elim {A = A} {B} x y z) = lemma-∨-elim Γ A B C (sound Γ (A ∨ B) x ) (sound (Γ , A) C y ) (sound (Γ , B) C z)  


-- ----------------------------------------------------------------------
-- * Bonus questions and beyond

-- If you feel adventurous, add more connectives, such as ¬A or A ∨ B,
-- to the boolean logic.
--
-- The proof rules are:
--
--    Γ, A ⊢ ⊥
-- ────────────── (¬-intro)
--     Γ ⊢ ¬A
--
--
--    Γ ⊢ ¬A     Γ ⊢ A
-- ───────────────────── (¬-elim)
--         Γ ⊢ ⊥
--
--
--      Γ ⊢ A
-- ───────────── (∨-intro1)
--    Γ ⊢ A ∨ B
--
-- 
--      Γ ⊢ B
-- ───────────── (∨-intro2)
--    Γ ⊢ A ∨ B
--
--
--    Γ ⊢ A ∨ B    Γ, A ⊢ C    Γ, B ⊢ C
-- ─────────────────────────────────────── (∨-elim)
--                  Γ ⊢ C

-- If you feel extremely ambitious, try to prove completeness, the
-- converse of soundness. Completeness is the statement that Γ ⊧ A
-- implies Γ ⊢ A.
--
-- Warning: this is extremely difficult and far more work than
-- soundness. Neither Frank nor I have been able to finish a proof of
-- completeness.

-- Actually, Peter had finished the proof a couple of days later using
-- conjunction normal form.

completeness-property : Set
completeness-property = ∀ Γ A -> Γ ⊧ A -> Γ ⊢ A

-- Now, I (Bian) will prove this property in Kalmar.agda using
-- Kalmar's lemma.
