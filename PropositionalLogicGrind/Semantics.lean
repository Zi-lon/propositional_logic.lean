import Mathlib.Data.Set.Basic
import PropositionalLogicGrind.Syntax

namespace Val

variable { α : Type u}

@[simp]
lemma bivalence_one (v : Val α) (ϕ : Fml α) :
    ⟦ ϕ , v ⟧ ≠ true → ⟦ ϕ , v ⟧ = false := by
    grind

@[simp]
lemma bot (v : Val α) : @eval α Fml.bot v = false := by
  rfl

@[simp]
lemma neg_true (ϕ : Fml α) (v : Val α) :
    ⟦¬ϕ , v⟧ = true ↔ (⟦ϕ , v⟧ = false) := by
  simp [eval]

@[simp]
lemma conj_true (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ∧ ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = true) ∧ (⟦ψ , v⟧ = true) := by
  simp only [eval]
  simp only [Bool.and_eq_true_iff]

@[simp]
lemma disj_true (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ∨ ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = true) ∨ (⟦ψ , v⟧ = true) := by
  simp only [eval]
  simp only [Bool.or_eq_true_iff]

@[simp]
lemma imp_true (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ → ψ , v⟧ = true ↔ (⟦ϕ , v⟧ = false) ∨ (⟦ψ , v⟧ = true) := by
      simp[Fml.imp]
end Val

namespace Consequence

variable { α : Type u}

@[simp]
lemma def_iff {Γ : Set (Fml α)} {ϕ : Fml α} :
    (Γ ⊨ ϕ) ↔ (∀ v : Val α, (∀ ψ ∈ Γ, ⟦ψ , v⟧ = true) → (⟦ϕ , v⟧ = true)) := by
  rfl

@[simp]
lemma monotonicity {Γ Δ : Set (Fml α)} {ϕ : Fml α}
    (h : Γ ⊨ ϕ) (g: Γ ⊆ Δ) : (Δ ⊨ ϕ) := by
    simp at h g
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
