import Mathlib.Data.Set.Basic
import PropositionalLogic.Syntax

namespace Val

variable { α : Type u}

@[simp]
lemma bivalence_one (v : Val α) (ϕ : Fml α) :
    ⟦ ϕ , v ⟧ ≠ true → ⟦ ϕ , v ⟧ = false := by
    intro hypothesis
    cases hypothesis_eval : eval ϕ v
    trivial
    contradiction

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
    intro v h_Δ
    apply h v
    intro ψ hψ
    have hψ_in_Δ : ψ ∈ Δ := g hψ
    exact h_Δ ψ hψ_in_Δ

lemma bot_elim {Γ : Set (Fml α)} {ϕ : Fml α} (h: Γ ⊨ ⊥) : (Γ ⊨ ϕ) := by
  simp[Val.bot] at h
  simp
  intro v h_ψ
  specialize h v
  rcases h with ⟨x, x_in_Γ, x_false⟩
  have x_true : ⟦x, v⟧ = true := h_ψ x x_in_Γ
  rw [x_false] at x_true
  contradiction

@[simp]
lemma neg_intro {Γ : Set (Fml α)} {ϕ : Fml α}
    (h : (Γ ∪ {ϕ}) ⊨ ⊥) : (Γ ⊨ ¬ϕ) := by
      simp at h
      simp
      intro v hypothesis
      by_contra neg_ϕ
      simp at neg_ϕ
      have h_exist := h v neg_ϕ
      rcases h_exist with ⟨x, x_in_Γ⟩
      have x_in := x_in_Γ.left
      have x_in_false := x_in_Γ.right
      have x_true := hypothesis x x_in
      rw [x_in_false] at x_true
      contradiction

@[simp]
lemma neg_elim {Γ Δ : Set (Fml α)} {ϕ : Fml α}
    (h : Γ ⊨ ϕ) (g : Δ ⊨ ¬ϕ) :
    ((Γ ∪ Δ) ⊨ ⊥) := by
    intro v h_ψ
    apply h_ψ
    simp at h g
    have h_ϕ : ⟦ϕ , v⟧ = true := by
     apply h v
     intro ψ hψ
     apply h_ψ
     simp
     left
     trivial
    have h_not_ϕ : ⟦ϕ , v⟧ = false := by
     apply g
     intro ψ hψ
     have imp := h_ψ ψ
     apply imp
     right
     exact hψ
    rw [h_ϕ] at h_not_ϕ
    contradiction

@[simp]
lemma conj_intro {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α}
    (h : Γ ⊨ ϕ) (g : Δ ⊨ ψ) : ((Γ ∪ Δ) ⊨ ϕ ∧ ψ) := by
      intro v ht
      simp
      constructor
      apply h v
      intro θ hθ
      apply ht
      simp
      constructor
      trivial
      apply g v
      intro hα hψ
      apply ht
      simp
      right
      trivial

@[simp]
lemma conj_elim_left {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊨ ϕ ∧ ψ):
    (Γ ⊨ ϕ):= by
    simp at h
    simp
    intro v hypothesis
    specialize h v hypothesis
    exact h.left

@[simp]
lemma conj_elim_right {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊨ ϕ ∧ ψ):
    (Γ ⊨ ψ):= by
      simp at h
      simp
      intro v hypothesis
      specialize h v hypothesis
      exact h.right

@[simp]
lemma disj_intro_left {Γ : Set (Fml α)} {ϕ ψ : Fml α}
  (h : Γ ⊨ ϕ) : (Γ ⊨ ϕ ∨ ψ) := by
    simp at h
    simp
    intro v γ
    specialize h v γ
    left
    trivial

@[simp]
lemma disj_intro_right {Γ : Set (Fml α)} {ϕ ψ : Fml α}
  (h : Γ ⊨ ψ) : (Γ ⊨ ϕ ∨ ψ) := by
    simp at h
    simp
    intro v γ
    specialize h v γ
    right
    trivial

@[simp]
lemma disj_elim {Γ Δ Ξ : Set (Fml α)} {ϕ ψ χ : Fml α}
  (h : Γ ⊨ (ϕ ∨ ψ)) (g : (Δ ∪ {ϕ}) ⊨ χ) (f : (Ξ ∪ {ψ}) ⊨ χ) : ((Γ ∪ Δ ∪ Ξ) ⊨ χ) := by
  intro v ht
  simp at h g f

  have hΓ : ∀ a ∈ Γ, ⟦a , v⟧ = true := by
   intro β hβ
   apply ht
   simp
   left
   left
   assumption

  have hΞ : ∀ a ∈ Ξ, ⟦a , v⟧ = true := by
   intro β hβ
   apply ht
   simp
   right
   assumption

  have hΔ : ∀ a ∈ Δ, ⟦a , v⟧ = true := by
   intro β hβ
   apply ht
   simp
   left
   right
   assumption

  specialize h v
  have h_rechts := h hΓ

  by_cases h_ϕ : ⟦ϕ , v⟧ = true
  exact g v h_ϕ hΔ
  simp [h_ϕ] at h_rechts
  exact f v h_rechts hΞ

@[simp]
lemma imp_intro {Γ : Set (Fml α)} {ϕ ψ : Fml α}
    (h : (Γ ∪ {ϕ}) ⊨ ψ ) : (Γ ⊨ ϕ → ψ) := by
    intro v hψ
    rw [Val.imp_true]
    simp at h
    by_cases h_ϕ : ⟦ϕ , v⟧
    right
    exact h v h_ϕ hψ
    simp [*] at h_ϕ
    left
    exact h_ϕ

@[simp]
lemma imp_elim {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊨ ϕ → ψ ) (g : Δ ⊨  ϕ ) :
    (Γ ∪ Δ) ⊨ ψ := by
    intro v hψ
    simp at h g
    have hΓ : ∀ α ∈ Γ, ⟦α, v⟧ = true := by
     intro α hα
     apply hψ
     simp
     left
     assumption
    have hΔ : ∀ α ∈ Δ, ⟦α, v⟧ = true := by
     intro α hα
     apply hψ α
     simp
     right
     assumption
    have h_h := h v hΓ
    have h_g := g v hΔ
    rcases h_h with h_false | h_true
    rw [h_g] at h_false
    contradiction
    assumption

@[simp]
lemma raa {Γ : Set (Fml α)} {ϕ : Fml α}
  (h: (Γ ∪ {¬ϕ}) ⊨ ⊥) : (Γ ⊨ ϕ) := by
  simp at h
  simp
  intro v ψ_in_Γ
  by_contra h_contra_ϕ
  have h_neg_ϕ : ⟦ϕ , v⟧ = false := by
   simp [h_contra_ϕ]
  obtain ⟨ψ, hψ, hψ_conc⟩ := h v h_neg_ϕ
  have hψ_true := ψ_in_Γ ψ hψ
  simp [hψ_true] at hψ_conc

end Consequence
