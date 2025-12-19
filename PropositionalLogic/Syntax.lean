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
  | bot, i, ψ       => bot
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

namespace Countable

variable [Countable α]

def fromNat : ℕ → Fml α
  | 0 => ⊥
  | n + 1 => ¬ fromNat n

@[simp]
lemma cxty_fromNat (n : ℕ) : cxty (fromNat (α := α) n) = n := by
  induction n with
  | zero =>
      simp [fromNat, cxty_bot]
  | succ n ih =>
      simp [fromNat, ih, cxty_neg]

lemma fromNat_injective : Function.Injective (fromNat (α := α)) := by
  intro m n h
  have := congrArg cxty h
  simpa [cxty_fromNat] using this

/-- A (noncomputable) canonical equivalence between `ℕ` and `Fml α`
when the variable type `α` is countable. -/
noncomputable def equivNat : ℕ ≃ Fml α := by
  classical
  let toFun : ℕ ↪ Fml α :=
    ⟨fromNat (α := α), fromNat_injective (α := α)⟩
  have h := Countable.exists_injective_nat (Fml α)
  let invFun : Fml α ↪ ℕ := ⟨h.choose, h.choose_spec⟩
  exact (Function.Embedding.antisymm toFun invFun).some

/-- Canonical enumeration of formulas by natural numbers. -/
noncomputable def numbering (n : ℕ) : Fml α :=
  equivNat n

/-- Canonical index of a formula as a natural number. -/
noncomputable def index (φ : Fml α) : ℕ :=
  equivNat.symm φ

@[simp]
lemma numbering_index (φ : Fml α) :
    numbering (index φ) = φ := by
      unfold numbering index
      grind

@[simp]
lemma index_numbering (n : ℕ) :
    index (numbering n : Fml α) = n := by
  unfold numbering index
  grind

end Countable

end Fml

inductive Lit (α : Type u) where
  | bot : Lit α
  | top : Lit α
  | pos : α → Lit α
  | neg : α → Lit α
  deriving DecidableEq, Countable

namespace Lit

-- variable {α : Type u}
--
-- -- notation "p" => pos
-- -- notation "p̅" => neg
-- -- notation "⊥" => bot
-- -- notation "⊤" => top
--
-- private def toStr [ToString α] : Lit α → String
--   | pos i     => "p" ++ toString i
--   | neg i     => "p̅" ++ toString i
--   | bot       => "⊥"
--   | top       => "⊤"
--
-- instance [ToString α] : Repr (Lit α) where
--   reprPrec f _ := toStr f
--
-- instance [ToString α] : ToString (Lit α) where
--   toString f := toStr f
--
-- def compl : Lit α → Lit α
--   | bot     => top
--   | top     => bot
--   | pos a   => neg a
--   | neg a   => pos a
--
--
-- -- This gives us, among other things, the notation `-l` for the complement of a
-- -- literal `l`.
-- instance : Neg (Lit α):=
--   ⟨compl⟩
--
-- @[simp] lemma compl_bot : -(⊥ : Lit α) = (⊤ : Lit α ):= by
--   rfl
--
-- @[simp] lemma compl_top : -(⊤ : Lit α) = (⊥ : Lit α) := by
--   rfl
--
-- @[simp] lemma compl_pos (a : α) : -(pos a) = neg a := by
--   rfl
--
-- @[simp] lemma compl_neg (a : α) : -(neg a) = pos a := by
--   rfl
--
-- @[simp] lemma double_compl (l : Lit α) : -(-l) = l := by
--   cases l <;> rfl
--
-- def toFml : Lit α → Fml α
--   | bot     => Fml.bot
--   | top     => Fml.top
--   | pos a   => Fml.var a
--   | neg a   => Fml.neg (Fml.var a)
--
-- instance CoercionToFml : Coe (Lit α) (Fml α) :=
--   ⟨toFml⟩
--
-- end Lit
