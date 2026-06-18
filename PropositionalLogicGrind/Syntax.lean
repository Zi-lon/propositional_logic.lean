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
