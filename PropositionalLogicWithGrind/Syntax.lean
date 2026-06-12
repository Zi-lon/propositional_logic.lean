import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.Linarith
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.SchroederBernstein

import Lean

universe u

inductive Fml (α : Type u) where
  | var  : α → Fml α
  | bot  : Fml α
  | neg  : Fml α → Fml α
  | conj : Fml α → Fml α → Fml α
  | disj : Fml α → Fml α → Fml α
  deriving DecidableEq, Countable, Nonempty

variable {α : Type u}


-- # Eval
abbrev Val (α : Type u) := α → Bool

def eval : Fml α → Val α → Bool
  | Fml.bot, _      => false
  | Fml.var i, v    => v i
  | Fml.neg φ , v   => !(eval φ v)
  | Fml.conj φ ψ, v => ((eval φ v) && (eval ψ v))
  | Fml.disj φ ψ, v => (eval φ v) || (eval ψ v)

instance : CoeFun (Val α) (fun _ => Fml α → Bool) where
  coe v ϕ := eval ϕ v

notation "⟦" ϕ " , " v "⟧" => eval ϕ v
-- # End Eval


-- # Satisfiability
def Sat {α : Type u } (Γ : Set (Fml α)) : Prop :=
  ∃ v : Val α, (∀ψ ∈ Γ, ⟦ψ , v⟧ = true)
-- # End Satisfiability


-- # Consequence
def Consequence { α : Type u} (Γ : Set (Fml α)) (ϕ : Fml α) : Prop :=
  ∀ v : Val α, (∀ ψ ∈ Γ, ⟦ψ , v⟧ = true) → (⟦ϕ , v⟧ = true)

notation Γ " ⊨ " ϕ => Consequence Γ ϕ
notation Γ " ⊭ " ϕ => ¬ Consequence Γ ϕ
-- # End Consequence


-- # Validity
def Valid {α : Type u } (ϕ : Fml α) : Prop :=
  ∅ ⊨ ϕ

notation "⊨ " ϕ => Valid ϕ
-- # End Validity


--# Formules
namespace Fml

variable {α : Type u}

def top : Fml α := neg bot
def imp (φ ψ : Fml α) : Fml α := disj (neg φ) ψ
def iff (f g : Fml α) : Fml α := conj (imp f g) (imp g f)

notation "p" => var
notation "⊥" => bot
notation "⊤" => top

prefix:40 " ¬ " => neg
infixr:35 " ∧ " => conj
infixr:30 " ∨ " => disj
infixr:25 " → " => imp
infixr:25 " ↔ " => iff

private def toStr [ToString α] : Fml α → String
  | var i     => toString i
  | bot       => "⊥"
  | neg ϕ     => "¬" ++ toStr ϕ
  | conj φ ψ  => "(" ++ toStr φ ++ " ∧ " ++ toStr ψ ++ ")"
  | disj φ ψ  => "(" ++ toStr φ ++ " ∨ " ++ toStr ψ ++ ")"

instance [ToString α] : Repr (Fml α) where
  reprPrec f _ := toStr f

instance [ToString α] : ToString (Fml α) where
  toString f := toStr f

def propVarList : Fml α → List α
  | var a => [a]
  | bot => []
  | neg φ => propVarList φ
  | conj φ ψ => propVarList φ ++ propVarList ψ
  | disj φ ψ => propVarList φ ++ propVarList ψ

def propVars [DecidableEq α] (φ : Fml α) : Finset α :=
  (propVarList φ).toFinset

def subfmlList [DecidableEq α]  : Fml α → List (Fml α)
  | var a    => [var a]
  | ⊥      => [⊥]
  | neg φ    => φ :: subfmlList φ
  | conj φ ψ => φ :: ψ :: (subfmlList φ ++ subfmlList ψ)
  | disj φ ψ => φ :: ψ :: (subfmlList φ ++ subfmlList ψ)

def subfmls (φ : Fml α) [DecidableEq α] : Finset (Fml α) :=
  (subfmlList φ).toFinset

def cxty : Fml α → Nat
  | var _    => 0
  | ⊥        => 0
  | neg φ     => cxty φ + 1
  | conj φ ψ   => max (cxty φ) (cxty ψ) + 1
  | disj φ ψ   => max (cxty φ) (cxty ψ) + 1

notation "c(" φ ")" => cxty φ

@[simp]
lemma cxty_var (a : α) : c(var a) = 0 := by
  rfl

@[simp]
lemma cxty_bot : cxty (⊥ : Fml α) = 0 := by
  rfl

@[simp]
lemma cxty_neg (φ : Fml α) : c(¬ φ) = c(φ) + 1 := by
  rfl

@[simp]
lemma cxty_conj (φ ψ : Fml α) : c(φ ∧ ψ) = (max c(φ) c(ψ)) + 1 := by
  rfl

@[simp]
lemma cxty_disj (φ ψ : Fml α) : c(φ ∨ ψ) = (max c(φ) c(ψ)) + 1 := by
  rfl

def ltc (f g : Fml α) : Prop := cxty f < cxty g

notation φ "≺" ψ => ltc φ ψ

lemma wf_lc : WellFounded (ltc : Fml α → Fml α → Prop) := by
  simpa [ltc] using
    (measure cxty).wf

def induct_on_cxty {P : Fml α → Prop} (φ : Fml α)
  (h : ∀ ψ, (∀ χ, cxty χ < cxty ψ → P χ) → P ψ) : P φ :=
  WellFounded.induction wf_lc φ h

def subs [DecidableEq  α] : Fml α → α → Fml α → Fml α
  | var i, j, θ     => if i = j then θ else var i
  | bot, _, _       => bot
  | neg ϕ, i, θ     => neg (subs ϕ i θ)
  | conj ϕ ψ, i, θ  => conj (subs ϕ i θ) (subs ψ i θ)
  | disj ϕ ψ, i, θ  => disj (subs ϕ i θ) (subs ψ i θ)

notation φ "[" i "↦" ψ "]" => subs φ i ψ

@[simp]
lemma subs_var_eq_id [DecidableEq α] (i : α) (ϕ : Fml α) :
    (p i)[i ↦ ϕ] = ϕ := by
      simp[subs]

@[simp]
lemma subs_var_neq_id [DecidableEq α] (i j : α) (h : i ≠ j) (ϕ : Fml α) :
    (p i)[j ↦ ϕ] = p i := by
      simp[subs, h]

@[simp]
lemma subs_bot_eq_id [DecidableEq α] (i : α) (ϕ : Fml α) :
    (⊥ : Fml α)[i ↦ ϕ] = ⊥ := by
      rfl

@[simp]
lemma subs_neg [DecidableEq α] (ϕ : Fml α) (i : α) (ψ : Fml α) :
    (¬ϕ)[i ↦ ψ] = (¬(ϕ[i ↦ ψ])) := by
      rfl

@[simp]
lemma subs_conj [DecidableEq α] (ϕ : Fml α) (i : α) (ψ θ : Fml α) :
    (ϕ ∧ ψ)[i ↦ θ] = (ϕ[i ↦ θ] ∧ ψ[i ↦ θ]) := by
      rfl

@[simp]
lemma subs_disj [DecidableEq α] (ϕ : Fml α) (i : α) (ψ θ : Fml α) :
    (ϕ ∨ ψ)[i ↦ θ] = (ϕ[i ↦ θ] ∨ ψ[i ↦ θ]) := by
      rfl

def big_disj (Γ : List (Fml α)) : Fml α :=
  Γ.foldr Fml.disj (⊥ : Fml α)

def big_conj (Γ : List (Fml α)) : Fml α :=
  Γ.foldr Fml.conj (⊤ : Fml α)

notation "⋀ " Γ => big_conj Γ
notation "⋁ " Γ => big_disj Γ

noncomputable def big_conj_finset (Γ : Finset (Fml α)) : Fml α :=
  big_conj Γ.toList

noncomputable def big_disj_finset (Γ : Finset (Fml α)) : Fml α :=
  big_disj Γ.toList

notation "⋀" Γ  => big_conj_finset Γ
notation "⋁" Γ => big_disj_finset Γ

@[simp]
lemma big_conj_nil : (⋀ [] : Fml α) = ⊤ := by
  rfl

@[simp]
lemma big_disj_nil : (⋁ [] : Fml α) = ⊥ := by
  rfl

@[simp]
lemma big_conj_cons (φ : Fml α) (Γ : List (Fml α)) :
    (⋀ (φ :: Γ) : Fml α) = (φ ∧ (⋀ Γ)) := by
      rfl

@[simp]
lemma big_disj_cons (φ : Fml α) (Γ : List (Fml α)) :
    (⋁ (φ :: Γ) : Fml α) = (φ ∨ (⋁ Γ)) := by
      rfl

-- # Der
inductive Der : Set (Fml α) → Fml α → Type u where
  | ass {ϕ : Fml α} : Der {ϕ} ϕ
  | weak {Γ : Set (Fml α )} {ϕ ψ : Fml α} : Der Γ ϕ → Der (Γ ∪ {ψ}) ϕ
  | bot_elim {Γ : Set (Fml α)} {ϕ : Fml α} : Der Γ ⊥ → Der Γ ϕ
  | neg_intro {Γ ϕ} : Der (Γ ∪ {ϕ}) ⊥ → Der Γ (¬ϕ)
  | neg_elim {Γ Δ : Set (Fml α)} {ϕ : Fml α} : Der Γ ϕ → Der Δ (¬ϕ) → Der (Γ ∪ Δ) ⊥
  | conj_intro {Γ Δ ϕ ψ} : Der Γ ϕ → Der Δ ψ → Der (Γ ∪ Δ) (ϕ ∧ ψ)
  | conj_elim_left {Γ : Set (Fml α)} {ϕ ψ : Fml α} : Der Γ (ϕ ∧ ψ) → Der Γ ϕ
  | conj_elim_right  {Γ : Set (Fml α)} {ϕ ψ : Fml α} : Der Γ (ϕ ∧ ψ) → Der Γ ψ
  | disj_intro_left  {Γ : Set (Fml α)} {ϕ ψ : Fml α} : Der Γ ϕ → Der Γ (ϕ ∨ ψ)
  | disj_intro_right {Γ : Set (Fml α)} {ϕ ψ : Fml α} : Der Γ ψ → Der Γ (ϕ ∨ ψ)
  | disj_elim {Γ Δ Ξ : Set (Fml α)} {ϕ ψ χ : Fml α} :
      Der Γ (ϕ ∨ ψ) →
      Der (Δ ∪ {ϕ}) χ →
      Der (Ξ ∪ {ψ}) χ →
      Der (Γ ∪ Δ ∪ Ξ) χ
  | imp_intro {Γ : Set (Fml α)} {ϕ ψ : Fml α} : (Der (Γ ∪ {ϕ}) ψ) → (Der Γ (ϕ → ψ))
  | imp_elim {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α} : (Der Γ (ϕ → ψ)) → (Der Δ ϕ) → (Der (Γ ∪ Δ) ψ)
  | raa {Γ : Set (Fml α)} {ϕ : Fml α} : Der (Γ ∪ {¬ϕ}) ⊥ → Der Γ ϕ

def provable {α : Type u} (Γ : Set (Fml α)) (ϕ : Fml α) : Prop :=
  ∃ Δ : Set (Fml α), Δ ⊆ Γ ∧ Nonempty (Der Δ ϕ)

notation Γ " ⊢ " ϕ => provable Γ ϕ
-- # End Der
