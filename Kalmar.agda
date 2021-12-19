-- We use Kalmar's lemma to show completeness. See
-- https://iep.utm.edu/prop-log/
-- http://comet.lehman.cuny.edu/mendel/Adlogic/sem5.pdf

{-# OPTIONS --without-K --safe #-}
module Kalmar where

-- imports from stdlib.
import Data.Empty as DE
open import Data.Bool using (Bool ; not ; false ; true)

open import Data.Nat using (ℕ ; _≟_)
open import Data.Nat.Properties using (≡-decSetoid)

open import Data.Product renaming (_,_ to _,'_) using (_×_)

open import Data.List using (List ; map ; _++_ ; deduplicate ; _∷_ ; [])
open import Data.List.Relation.Unary.Unique.DecSetoid ≡-decSetoid using (Unique ; [] ; _∷_)
open import Data.List.Membership.DecPropositional _≟_ renaming (_∈_ to _∈ℕ_) using (_∉_)

open import Relation.Nullary as RN using (yes ; no) 
open import Data.List.Relation.Unary.Any using (Any ; here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong₂)

-- imports from my files.
open import PropLogic

-- ----------------------------------------------------------------------
-- Inspect.

-- When "f x" evaluates to some "y", pattern matching on "Inspect (f
-- x)" gives "y" and the proof that "f x ≡ y". We use this vesion of
-- inspect instead of the one in PropositionalEquality for convenience.
data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x ≡ y -> Inspect x

inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x refl


-- ----------------------------------------------------------------------
-- Definitons and lemmas.

-- Fix a formula by possibly negating it such that under the given
-- assignment, the fixed formula is true.
fix-formula : Assign -> Formula -> Formula
fix-formula a f with interp a f
... | true =  f
... | false = ¬ f

-- Fix a symbol by possibly negating it such that under the given
-- assignment, the fixed symbol is true. We call a natural number a
-- "symbol". (Recall P n is the nth propositional symbol)
fix-sym : Assign -> ℕ -> Formula
fix-sym a n with a n
... | true = P n
... | false = ¬ (P n)

-- Given an assignment and a list of symbols, return a context
-- consisting of "fixed symbols". We call a list of natural numbers
-- "symbol context" or "sctx". (recall context is a list of
-- formulas)
fix-sctx : Assign -> List ℕ -> Context
fix-sctx a = map (fix-sym a)

-- Given an assignment "a", and a symbol "v", return an new
-- assignment that negate "a v", and is the same as "a" in all other
-- symbols.
negate-assign-at : Assign -> ℕ -> (ℕ -> Bool)
negate-assign-at a m n with m ≟ n
... | no ¬p = a n
... | yes p = not (a n)


-- Lemmas about negate-assign-at.
lemma1-negate-assign-at : ∀ {a m n} -> RN.¬ (m ≡ n) -> negate-assign-at a m n ≡ a n
lemma1-negate-assign-at {a} {m} {n} neq with (m ≟ n) 
... | yes p  = DE.⊥-elim (neq p)
... | no _ = refl 

lemma2-negate-assign-at : ∀ {a m n} -> (m ≡ n) -> negate-assign-at a m n ≡ not (a n)
lemma2-negate-assign-at {a} {m} {.m} refl with m ≟ m
... | no ¬p = DE.⊥-elim (¬p refl)
... | yes p = refl

lemma-fix-sym : ∀ {a m n} -> RN.¬ m ≡ n -> fix-sym (negate-assign-at a m) n ≡ fix-sym a n
lemma-fix-sym {a} {m} {n} neq rewrite lemma1-negate-assign-at {a} {m} {n} neq = refl 

lemma-fix-sym-neg : ∀ {a n} -> (a n ≡ false) -> fix-sym (negate-assign-at a n) n ≡ (P n)
lemma-fix-sym-neg {a} {n} eq with  lemma2-negate-assign-at {a} {n} {n} refl
... | hyp rewrite hyp  | eq = refl 

lemma-fix-sym-pos : ∀ {a n} -> (a n ≡ true) -> fix-sym (negate-assign-at a n) n ≡ ¬ (P n)
lemma-fix-sym-pos {a} {n} eq with  lemma2-negate-assign-at {a} {n} {n} refl
... | hyp rewrite hyp  | eq = refl 


-- A lemma about fix-sctx.
lemma-fix-sctx : ∀ {a ns n} -> n ∉ ns -> fix-sctx (negate-assign-at a n) ns ≡ fix-sctx a ns
lemma-fix-sctx {a} {Empty} {n} nin = refl
lemma-fix-sctx {a} {ns , x} {n} nin = cong₂ _,_ (lemma-fix-sctx n∉ns) (lemma-fix-sym claim) 
  where
    open import Data.List.Relation.Unary.Any using (there ; here)
    n∉ns : n ∉ ns
    n∉ns = λ x₁ → nin (there x₁)
    claim : RN.¬ n ≡ x
    claim = λ x₁ → nin (here x₁) 

-- Given a formula, return the list of all the symbol in it
-- (allowing repeation).
syms-of-formula : Formula -> List ℕ
syms-of-formula (P x) = x ∷ []
syms-of-formula (A ∧ B) = (syms-of-formula A) ++ (syms-of-formula B) 
syms-of-formula (A ⇒ B) = (syms-of-formula A) ++ (syms-of-formula B) 
syms-of-formula ⊥ = []
syms-of-formula ⊤ = []
syms-of-formula (¬ f) = syms-of-formula f
syms-of-formula (A ∨ B) = (syms-of-formula A) ++ (syms-of-formula B) 


-- De Morgan's law.
demorg : ∀ {Γ A B} -> Γ ⊢ (¬ A) ∧ (¬ B) -> Γ ⊢ ¬ (A ∨ B)
demorg der = ¬-intro (∨-elim (assump ∈-base) (¬-elim (∧-elim1 (weakening der (λ z → ∈-step (∈-step z)))) (assump ∈-base)) ((¬-elim (∧-elim2 (weakening der (λ z → ∈-step (∈-step z)))) (assump ∈-base)))) 

demorg1 : ∀ {Γ A B} -> Γ ⊢ (¬ A) ∨ (¬ B) -> Γ ⊢ ¬ (A ∧ B)
demorg1 der = ¬-intro (∨-elim (weakening der ∈-step) (¬-elim (assump ∈-base) (∧-elim1 (assump (∈-step ∈-base)))) ((¬-elim (assump ∈-base) (∧-elim2 (assump (∈-step ∈-base)))))) 

-- Implication with a null hypothesis is always syntactically valid.
null-hyp : ∀ {Γ A B} -> Γ ⊢ (¬ A) -> Γ ⊢ A ⇒ B
null-hyp der = ⇒-intro (⊥-elim (¬-elim (weakening der ∈-step) (assump ∈-base)))

-- Implication with a null conclusion is always syntactically invalid.
null-conclusion : ∀ {Γ A B} -> Γ ⊢ A -> Γ ⊢ (¬ B) -> Γ ⊢ ¬ (A ⇒ B)
null-conclusion der1 der2 = ¬-intro (¬-elim (weakening der2 ∈-step) (⇒-elim (assump ∈-base) (weakening der1 ∈-step))) 

-- Double negation of "A" is valid if "A" is valid.
double-negate : ∀ {Γ A} -> Γ ⊢ A -> Γ ⊢ ¬ (¬ A)  
double-negate der = ¬-intro (¬-elim (assump ∈-base) (weakening der ∈-step)) 

-- ----------------------------------------------------------------------
-- List containment.

-- In file "Logic", membership and context containment are defined
-- similarly but differently from the one in stdlib. we have to do a
-- translation.
infix 3 _⊂_
_⊂_ : List ℕ ->  List ℕ -> Set
xs ⊂ ys = ∀ {x} -> x ∈ℕ xs -> x ∈ℕ ys

-- Lemma: membership is functorial. 
lemma-fix-sym-∈ : ∀ {ρ} {x} {ys} -> x ∈ℕ ys -> fix-sym ρ x ∈ fix-sctx ρ ys
lemma-fix-sym-∈ {ρ} {x} {.(_ , x₁)} (here {x₁} px) rewrite px = ∈-base
lemma-fix-sym-∈ {ρ} {x} {.(xs , x₁)} (there {x₁} {xs} hyp) = ∈-step (lemma-fix-sym-∈ hyp)

-- Lemma: removing the head element preserves containment. 
lemma-⊂-rh : ∀ {x : ℕ} {xs ys} -> (x ∷ xs) ⊂ ys -> xs ⊂ ys
lemma-⊂-rh {x} {.(_ , _)} {ys} sub (here px) rewrite px = sub (there (here refl))
lemma-⊂-rh {x} {.(_ , _)} {ys} sub (there hyp) = sub (there (there hyp))

-- Lemma: List containment is functorial.
lemma-map : ∀ {ρ xs ys} -> xs ⊂ ys -> fix-sctx ρ xs ⊆ fix-sctx ρ ys
lemma-map {ρ} {Empty} {ys} sub = λ {()}
lemma-map {ρ} {xs , x} {ys} sub = λ { ∈-base → lemma-fix-sym-∈ (sub (here refl)) ; (∈-step x₁) → lemma-map (lemma-⊂-rh sub) x₁}

-- ----------------------------------------------------------------------
-- Kalmar's Lemma.

mutual 
  -- We use aux to abstract over similar codes. 
  aux : ∀ ρ F G ->
    let Γ = fix-sctx ρ (syms-of-formula F ++ syms-of-formula G) in    
    Γ ⊢ (fix-formula ρ F) × Γ ⊢ (fix-formula ρ G) 
  aux ρ F G = let vl = syms-of-formula F in let vr = syms-of-formula G in
      weakening (lemma-Kalmar {F} ρ) (lemma-map {ρ} {vl} {vl ++ vr} ∈-++⁺ˡ)
      ,' weakening (lemma-Kalmar {G} ρ) (lemma-map {ρ} {vr} {vl ++ vr} (∈-++⁺ʳ vl {ys = vr}))
      where
        open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ ; ∈-++⁺ʳ)

  lemma-Kalmar : ∀ {F} ρ -> fix-sctx ρ (syms-of-formula F) ⊢ fix-formula ρ F
  lemma-Kalmar {P x} ρ  with ρ x
  ... | true =  assump ∈-base
  ... | false = assump ∈-base
  lemma-Kalmar {F ∧ F₁} ρ with inspect (interp ρ F) | inspect (interp ρ F₁) | aux ρ F F₁
  ... | it false x | it false x₁ | iha ,' ihb rewrite x | x₁ = demorg1 (∨-intro2 ihb)  
  ... | it false x | it true x₁ | iha ,' ihb rewrite x | x₁ = demorg1 (∨-intro1 iha)
  ... | it true x | it false x₁ | iha ,' ihb rewrite x | x₁ = demorg1 (∨-intro2 ihb) 
  ... | it true x | it true x₁ | iha ,' ihb rewrite x | x₁ = ∧-intro iha ihb
  lemma-Kalmar {F ⇒ F₁} ρ with inspect (interp ρ F) | inspect (interp ρ F₁) | aux ρ F F₁
  ... | it true x | it true x₁ | iha ,' ihb rewrite x | x₁  = ⇒-intro (weakening ihb ∈-step) 
  ... | it false x | it true x₁ | iha ,' ihb rewrite x | x₁  = ⇒-intro (weakening ihb ∈-step)  
  ... | it true x | it false x₁ | iha ,' ihb rewrite x | x₁  = null-conclusion iha ihb 
  ... | it false x | it false x₁ | iha ,' ihb rewrite x | x₁  = null-hyp iha 
  lemma-Kalmar {F ∨ F₁} ρ with inspect (interp ρ F) | inspect (interp ρ F₁) | aux ρ F F₁
  ... | it true x | it true x₁ | iha ,' ihb rewrite x | x₁  = ∨-intro1 iha 
  ... | it false x | it true x₁ | iha ,' ihb rewrite x | x₁  = ∨-intro2 ihb 
  ... | it true x | it false x₁ | iha ,' ihb rewrite x | x₁  = ∨-intro1 iha 
  ... | it false x | it false x₁ | iha ,' ihb rewrite x | x₁  = demorg (∧-intro iha ihb) 
  lemma-Kalmar  {⊥} ρ = ¬-intro (assump ∈-base)
  lemma-Kalmar  {⊤} ρ = ⊤-intro
  lemma-Kalmar  {¬ F}  ρ with inspect (interp ρ F) | lemma-Kalmar {F} ρ
  ... | it false x | ih rewrite x = ih
  ... | it true x | ih rewrite x = double-negate ih

-- ----------------------------------------------------------------------
-- Unique symbol context.

-- The idea is that the deduplicated symbol context is as strong as
-- the original one. For the former, we can make two assignments such
-- that they only differs at one symbol, i.e. the head symbol. Then by
-- using ∨-elim we can reduce the symbol context by removing the head.

-- Lemma: "symbol context version" of weakening. 
weakening-sym : ∀ {ρ xs ys F} -> xs ⊂ ys -> fix-sctx ρ xs ⊢ F -> fix-sctx ρ ys ⊢ F
weakening-sym {ρ} {xs} {ys} {F} sub hyp = weakening hyp (lemma-map sub) 

-- Lemma: Deduplicated symbol ctx is as strong as the original ctx.
lemma-dedup : ∀ {ρ xs F} ->  fix-sctx ρ xs ⊢ F -> fix-sctx ρ (deduplicate _≟_ xs) ⊢ F
lemma-dedup {xs = xs} = weakening-sym λ x → ∈-deduplicate⁺ _≟_ {xs} x
 where
   open import Data.List.Membership.Propositional.Properties using (∈-deduplicate⁺)

-- law of excluded middle is derivable.
ex-mid : ∀ {A} -> Empty ⊢ (¬ A) ∨ A
ex-mid {A} = ∨-elim step (∨-intro1 (¬-intro (⇒-elim (assump (∈-step ∈-base)) (assump ∈-base)))) (∨-intro2 (double-negation (⇒-intro (⇒-elim (assump (∈-step ∈-base)) (¬-intro (⇒-elim (assump (∈-step ∈-base)) (assump ∈-base)))))))
  where
    demorgan : ∀ {A B} -> Empty ⊢ ((A ∧ B) ⇒ ⊥) ⇒ (A ⇒ ⊥) ∨ (B ⇒ ⊥)
    demorgan = ⇒-intro (double-negation (⇒-intro (⇒-elim (assump ∈-base) (∨-intro1 (⇒-intro (⇒-elim (assump (∈-step ∈-base)) (∨-intro2 (⇒-intro (⇒-elim (assump (∈-step (∈-step (∈-step ∈-base)))) (∧-intro (assump (∈-step ∈-base)) (assump ∈-base)))))))))))  
    step : Empty ⊢ ((A ⇒ ⊥) ∨ ((¬ A) ⇒ ⊥)) 
    step = ⇒-elim (demorgan {A} {¬ A}) (⇒-intro (¬-elim (∧-elim2 (assump ∈-base)) (∧-elim1 (assump ∈-base)))) 
-- ∨-elim instantiated using excluded middle. 
∨-elim-exmid : ∀ {Γ A B} -> Γ , ¬ A ⊢ B -> Γ , A ⊢ B -> Γ ⊢ B
∨-elim-exmid {Γ} {A} {b} d e = ∨-elim (weakening ex-mid lemma-⊆-empty) d e

-- Lemma: Removing one symbol from symbol context. 
lemma-sctx-reduce : ∀ {ρ ns n F} -> (n ∉ ns) ->
  fix-sctx ρ (n ∷ ns) ⊢ F ->
  fix-sctx (negate-assign-at ρ n) (n ∷ ns) ⊢ F ->
  fix-sctx ρ ns ⊢ F
lemma-sctx-reduce {ρ} {ns} {n} {F} nin h1 h2 with inspect (ρ n)
... | it false pf rewrite (lemma-fix-sctx {a = ρ} nin) | lemma-fix-sym-neg {ρ} {n} pf | pf = ∨-elim-exmid h1 h2
... | it true pf rewrite (lemma-fix-sctx {a = ρ} nin) | lemma-fix-sym-pos {ρ} {n} pf | pf = ∨-elim-exmid h2 h1 

-- lemma: if the symbol ctx is unique, we can repeatedly use
-- lemma-sctx-reduce to get an Empty context.
lemma-unique-ctx-reduce : ∀ {F} {ns : List ℕ} -> Unique (ns) -> (∀ ρ -> fix-sctx ρ ns ⊢ F) -> Empty ⊢ F
lemma-unique-ctx-reduce {F} {.Empty} [] hyp = hyp (λ _ → false)
lemma-unique-ctx-reduce {F} {.(xs , x₁)} (_∷_ {x = x₁} {xs = xs} x uns) hyp = ih
  where
    open import Data.List.Relation.Unary.All
    open import Function
    anyAll : ∀ {ys : List ℕ} {Pd : ℕ -> Set} -> Any Pd ys -> RN.¬ (All (RN.¬_ ∘ Pd) ys)
    anyAll {.(_ , _)} {Pd} (here px) (px₁ ∷ all₁) = px₁ px
    anyAll {.(xs , _)} {Pd} (there {xs = xs} any₁) (px ∷ all₁) = anyAll {xs} {Pd} any₁ all₁
    x₁∉xs : x₁ ∉ xs
    x₁∉xs h = anyAll h x
    ih : Empty ⊢ F
    ih = lemma-unique-ctx-reduce {F} {xs} uns λ ρ → lemma-sctx-reduce {ρ} {xs} {x₁} {F} x₁∉xs (hyp ρ) (hyp (negate-assign-at ρ x₁)) 


-- ----------------------------------------------------------------------
-- Completeness.

-- lemma-Kalmar instantiated with semantical entailment.
lemma-Kalmar-⊧ : ∀ {ρ F} -> Empty ⊧ F -> fix-sctx ρ (syms-of-formula F) ⊢ F
lemma-Kalmar-⊧ {ρ} {F} st with lemma-Kalmar {F} ρ | st ρ refl 
... | kal | Ft rewrite Ft = kal 

-- lemma-dedup instantiated with semantical entailment.
lemma-dedup-⊧ : ∀ {F} -> Empty ⊧ F -> (∀ ρ -> fix-sctx ρ (deduplicate _≟_  (syms-of-formula F)) ⊢ F)
lemma-dedup-⊧ st = λ ρ → lemma-dedup (lemma-Kalmar-⊧ (λ ρ _ → st ρ refl)) 

-- | Completeness in empty context.
completeness-empty : ∀ {F} -> Empty ⊧ F -> Empty ⊢ F
completeness-empty {F} st = lemma-unique-ctx-reduce (deduplicate-! ≡-decSetoid (syms-of-formula F)) (lemma-dedup-⊧ {F} st)
  where
    open import Data.List.Relation.Unary.Unique.DecSetoid.Properties using (deduplicate-!) 

-- | completeness-property. 
completeness : ∀ Γ A -> Γ ⊧ A -> Γ ⊢ A
completeness Empty A hyp = completeness-empty {A} hyp
completeness (Γ , B) A hyp = ⇒-elim (weakening (completeness Γ (B ⇒ A) (lemma-⇒-intro Γ B A hyp)) ∈-step) (assump ∈-base)
