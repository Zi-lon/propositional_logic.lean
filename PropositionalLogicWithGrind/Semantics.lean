import Mathlib.Data.Set.Basic
import PropositionalLogic.Syntax

-- # Eval
namespace Val

variable { α : Type u}

@[simp]
lemma bivalence_one (v : Val α) (ϕ : Fml α) :
    ⟦ ϕ , v ⟧ ≠ true → ⟦ ϕ , v ⟧ = false := by
    grind

@[simp]
lemma bivalence_two (v : Val α) (ϕ : Fml α) :
    ⟦ ϕ , v ⟧ ≠ false → ⟦ ϕ , v ⟧ = true := by
    grind

@[simp]
lemma bot (v : Val α) : @eval α Fml.bot v = false := by
  rfl

@[simp]
lemma top (v : Val α) : @eval α Fml.top v = true := by
  rfl

@[simp]
lemma bot_ne_true (v : Val α) : @eval α Fml.bot v ≠ true := by
  simp [eval]

@[simp]
lemma neg_true (ϕ : Fml α) (v : Val α) :
    ⟦¬ϕ , v⟧ = true ↔ (⟦ϕ , v⟧ = false) := by
  simp [eval]

@[simp]
lemma neg_false (ϕ : Fml α) (v : Val α) :
    ⟦¬ϕ , v⟧ = false ↔ (⟦ϕ , v⟧ = true) := by
  simp [eval]

@[simp]
lemma conj_true (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ∧ ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = true) ∧ (⟦ψ , v⟧ = true) := by
  simp only [eval]
  simp only [Bool.and_eq_true_iff]

@[simp]
lemma conj_false (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ∧ ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = false) ∨ (⟦ψ , v⟧ = false) := by
      simp only [eval]
      simp only [Bool.and_eq_false_iff]

@[simp]
lemma disj_true (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ∨ ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = true) ∨ (⟦ψ , v⟧ = true) := by
  simp only [eval]
  simp only [Bool.or_eq_true_iff]

@[simp]
lemma disj_false (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ∨ ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = false) ∧ (⟦ψ , v⟧ = false) := by
  simp only [eval]
  simp only [Bool.or_eq_false_iff]

@[simp]
lemma imp_true (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ → ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = false) ∨ (⟦ψ , v⟧ = true) := by
      simp[Fml.imp]

@[simp]
lemma imp_false (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ → ψ , v⟧ = false ↔ (⟦ϕ , v⟧ = true) ∧ (⟦ψ , v⟧ = false) := by
      simp[Fml.imp]

@[simp]
lemma iff_true (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ↔ ψ , v⟧ = true ↔ ((⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = true)) := by
    simp [Fml.iff]
    grind

@[simp]
lemma iff_false (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ↔ ψ , v⟧ = false ↔ ((⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = false)) := by
    simp [Fml.iff]
    grind

@[simp]
lemma conj_top (ϕ : Fml α) (v : Val α) :
    ⟦ϕ ∧ ⊤ , v⟧ = ⟦ϕ , v⟧ := by
      simp[eval]

@[simp]
lemma disj_bot (ϕ : Fml α) (v : Val α) :
    ⟦ϕ ∨ ⊥ , v⟧ = ⟦ϕ , v⟧ := by
      simp[eval]

@[simp]
lemma big_conj_cons (φ : Fml α) (Γ : List (Fml α)) (v : Val α):
    ⟦⋀ (φ :: Γ), v ⟧ = ⟦(φ ∧ (⋀ Γ)) , v ⟧:= by
      rfl

@[simp]
lemma big_conj_true (Γ : List (Fml α)) (v : Val α) :
    ⟦⋀ Γ , v⟧ = true ↔ ∀ ϕ ∈ Γ, ⟦ϕ , v⟧ = true := by
      induction Γ with
      | nil => simp
      | @cons ψ Γ' ih => simp at ih
                         simp
                         grind

@[simp]
lemma big_conj_finset_true (Γ : Finset (Fml α)) (v : Val α) :
    ⟦⋀ Γ , v⟧ = true ↔ ∀ ϕ ∈ Γ, ⟦ϕ , v⟧ = true := by
      unfold Fml.big_conj_finset
      simp

@[simp]
lemma big_conj_false (Γ : List (Fml α)) (v : Val α) :
    ⟦⋀ Γ , v⟧ = false ↔ ∃ ϕ ∈ Γ, ⟦ϕ , v⟧ = false := by
      induction Γ with
      | nil => simp
      | @cons ψ Γ' ih => simp at ih
                         simp
                         grind

@[simp]
lemma big_conj_finset_false (Γ : Finset (Fml α)) (v : Val α) :
    ⟦⋀ Γ , v⟧ = false ↔ ∃ ϕ ∈ Γ, ⟦ϕ , v⟧ = false := by
      unfold Fml.big_conj_finset
      simp
end Val
-- # End Eval


-- # Satisfiability
namespace Sat

variable { α : Type u}

@[simp]
lemma truth_monotone {v : Val α } {Γ Δ : Set (Fml α )} (h : Γ ⊆ Δ) (g : ∀ψ ∈  Δ, ⟦ψ , v ⟧ = true) :
    ∀ψ ∈  Γ, ⟦ψ , v ⟧ = true := by
    grind

@[simp]
lemma not_sat_iff_some_false (Γ : Set (Fml α)) : ¬ Sat Γ ↔ ∀ v : Val α, ∃ ψ ∈ Γ, ⟦ψ , v ⟧ = false := by
  simp[Sat]

@[simp]
lemma sat_monotone {Γ Δ : Set (Fml α )} (h : Sat Δ) (g : Γ ⊆ Δ) : Sat Γ := by
   simp[Sat] at h
   obtain ⟨v, hv⟩ := h
   simp[Sat]
   apply Exists.intro v
   apply truth_monotone g
   trivial

end Sat
-- # End Satisfiability


-- # Logical Consequence
namespace Consequence

variable { α : Type u}

@[simp]
lemma def_iff {Γ : Set (Fml α)} {ϕ : Fml α} :
    (Γ ⊨ ϕ) ↔ (∀ v : Val α, (∀ ψ ∈ Γ, ⟦ψ , v⟧ = true) → (⟦ϕ , v⟧ = true)) := by
  rfl

@[simp]
lemma consequence_iff_not_sat {Γ : Set (Fml α)} :
  ∀ ϕ : Fml α, (Γ ⊨ ϕ) ↔ ¬ Sat (Γ ∪ {¬ϕ}) := by
  simp[Sat]
  grind

@[simp]
lemma non_consequence_iff_sat {Γ : Set (Fml α)} (ϕ : Fml α) :
  (Γ ⊭ ϕ) ↔ Sat (Γ ∪ {¬ϕ}) := by
  simp[Sat]
  grind

@[simp]
lemma refl {Γ : Set (Fml α)} {ϕ : Fml α} (mem : ϕ ∈ Γ) : (Γ ⊨ ϕ) := by
  simp
  grind

@[simp]
lemma monotonicity {Γ Δ : Set (Fml α)} {ϕ : Fml α}
    (h : Γ ⊨ ϕ) (g: Γ ⊆ Δ) : (Δ ⊨ ϕ) := by
    simp at h g
    simp
    grind

@[simp]
lemma trans {Γ Δ : Set (Fml α)} {ϕ : Fml α} (h : Γ ⊨ ϕ) (_ : (Δ ∪ {ϕ}) ⊨ ϕ) : ((Γ ∪ Δ) ⊨ ϕ) := by
  simp at h
  simp
  grind

lemma bot_elim {Γ : Set (Fml α)} {ϕ : Fml α} (h: Γ ⊨ ⊥) : (Γ ⊨ ϕ) := by
  simp[Val.bot] at h
  simp
  intro v t
  specialize h v
  grind

@[simp]
lemma neg_intro {Γ : Set (Fml α)} {ϕ : Fml α}
    (h : (Γ ∪ {ϕ}) ⊨ ⊥) : (Γ ⊨ ¬ϕ) := by
    simp at h
    simp
    grind

@[simp]
lemma neg_elim {Γ Δ : Set (Fml α)} {ϕ : Fml α}
    (h : Γ ⊨ ϕ) (g : Δ ⊨ ¬ϕ) :
    ((Γ ∪ Δ) ⊨ ⊥) := by
    simp at h g
    simp
    intro v
    specialize h v
    grind

@[simp]
lemma conj_intro {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α}
    (h : Γ ⊨ ϕ) (g : Δ ⊨ ψ) : ((Γ ∪ Δ) ⊨ ϕ ∧ ψ) := by
    simp at h g
    simp
    grind

@[simp]
lemma conj_elim_left {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊨ ϕ ∧ ψ):
    (Γ ⊨ ϕ):= by
    simp at h
    simp
    grind

@[simp]
lemma conj_elim_right {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊨ ϕ ∧ ψ):
    (Γ ⊨ ψ):= by
      simp at h
      simp
      grind

@[simp]
lemma disj_intro_left {Γ : Set (Fml α)} {ϕ ψ : Fml α}
  (h : Γ ⊨ ϕ) : (Γ ⊨ ϕ ∨ ψ) := by
    simp at h
    simp
    grind

@[simp]
lemma disj_intro_right {Γ : Set (Fml α)} {ϕ ψ : Fml α}
  (h : Γ ⊨ ψ) : (Γ ⊨ ϕ ∨ ψ) := by
    simp at h
    simp
    grind

@[simp]
lemma disj_elim {Γ Δ Ξ : Set (Fml α)} {ϕ ψ χ : Fml α}
  (h : Γ ⊨ (ϕ ∨ ψ)) (g : (Δ ∪ {ϕ}) ⊨ χ) (f : (Ξ ∪ {ψ}) ⊨ χ) : ((Γ ∪ Δ ∪ Ξ) ⊨ χ) := by
  simp at h g f
  simp
  grind

@[simp]
lemma imp_intro {Γ : Set (Fml α)} {ϕ ψ : Fml α}
    (h : (Γ ∪ {ϕ}) ⊨ ψ ) : (Γ ⊨ ϕ → ψ) := by
    simp at h
    simp[Val.imp_true]
    grind

@[simp]
lemma imp_elim {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊨ ϕ → ψ ) (g : Δ ⊨  ϕ ) :
    (Γ ∪ Δ) ⊨ ψ := by
    simp at h g
    simp [*]
    grind

@[simp]
lemma raa {Γ : Set (Fml α)} {ϕ : Fml α}
  (h: (Γ ∪ {¬ϕ}) ⊨ ⊥) : (Γ ⊨ ϕ) := by
  simp at h
  simp
  grind

end Consequence
-- # End Consequence

-- # Valid
namespace Valid

variable { α : Type u}

@[simp]
lemma valid_iff {ϕ : Fml α} :
    (⊨ ϕ) ↔  ∀ v : Val α, ⟦ϕ , v⟧ = true := by
      simp[Valid, Consequence.def_iff]

@[simp]
lemma bivalid_iff {ϕ : Fml α} :
    (⊨ ϕ) ↔ ¬ Sat {¬ϕ} := by
      simp[Valid]

@[simp]
lemma law_of_excluded_middle (ϕ : Fml α) :
    ⊨ ϕ ∨ ¬ϕ := by
      simp[Valid]

@[simp]
lemma law_of_non_contradiction (ϕ : Fml α) :
    ⊨ ¬(ϕ ∧ ¬ϕ) := by
      simp[Valid]

@[simp]
lemma consequence_to_valid {Γ : Finset (Fml α)} {ϕ : Fml α} :
    (Γ ⊨ ϕ ) → ⊨ (⋀ Γ) → ϕ := by
      simp
      grind

end Valid
-- # End Valid


-- # Equivalence
-- # Eqv
def Eqv {α : Type u} (ϕ ψ : Fml α) : Prop :=
  ⊨ (ϕ ↔ ψ)

notation ϕ " ⟚ " ψ => Eqv ϕ ψ
-- # End Eqv

namespace Eqv
variable {α : Type u}

@[simp]
lemma equivalence_to_implication (ϕ ψ : Fml α) :
    (ϕ ⟚ ψ) ↔ (⊨ (ϕ → ψ)) ∧ (⊨ (ψ → ϕ)) := by
    simp[Eqv, Valid.valid_iff, Fml.iff]
    grind

@[simp]
lemma refl (ϕ : Fml α) : ϕ ⟚ ϕ := by
  simp[Eqv]

@[simp]
lemma symm {ϕ ψ : Fml α} (h : ϕ ⟚ ψ) : ψ ⟚ ϕ := by
  simp[Eqv] at h
  simp[Eqv]
  grind

@[simp]
lemma iff_negation {ϕ ψ : Fml α} (h : ϕ ⟚ ψ) : (¬ϕ) ⟚ (¬ψ) := by
  simp[Eqv] at h
  simp[Eqv]
  grind

@[simp]
lemma iff_conjunction {ϕ₁ ϕ₂ ψ₁ ψ₂ : Fml α}
  (h₁ : ϕ₁ ⟚ ψ₁) (h₂ : ϕ₂ ⟚ ψ₂) : (ϕ₁ ∧ ϕ₂) ⟚ (ψ₁ ∧ ψ₂) := by
  simp [Eqv] at h₁ h₂
  simp [Eqv]
  grind

end Eqv
-- # End Equivalence
