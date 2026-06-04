import Mathlib.Data.Set.Basic
import PropositionalLogic.Syntax

universe u

abbrev Val (α : Type u) := α → Bool

namespace Val

variable {α : Type u}

def eval : Fml α → Val α → Bool
  | Fml.bot, _      => false
  | Fml.var i, v    => v i
  | Fml.neg φ , v   => !(eval φ v)
  | Fml.conj φ ψ, v => ((eval φ v) && (eval ψ v))
  | Fml.disj φ ψ, v => (eval φ v) || (eval ψ v)

instance : CoeFun (Val α) (fun _ => Fml α → Bool) where
  coe v ϕ := eval ϕ v

notation "⟦" ϕ " , " v "⟧" => eval ϕ v

@[simp]
lemma bivalence_one (v : Val α) (ϕ : Fml α) :
    ⟦ ϕ , v ⟧ ≠ true → ⟦ ϕ , v ⟧ = false := by
    simp

@[simp]
lemma bivalence_two (v : Val α) (ϕ : Fml α) :
    ⟦ ϕ , v ⟧ ≠ false → ⟦ ϕ , v ⟧ = true := by
      intro hypothesis
      cases hypotheis_eval : eval ϕ v
      contradiction
      rfl

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
      constructor
      intro h
      constructor
      intro h_links
      simp [Fml.iff] at h
      have h_left : ⟦ϕ , v⟧ = false ∨ ⟦ψ , v⟧ = true := h.left
      rw [h_links] at h_left
      simp at h_left
      trivial

      intro h_rechts
      simp [Fml.iff] at h
      have h_right : ⟦ψ , v⟧ = false ∨ ⟦ϕ , v⟧ = true := h.right
      rw [h_rechts] at h_right
      simp at h_right
      trivial

      simp [Fml.iff]
      intro left
      by_cases h : ⟦ϕ , v⟧
      rw [h] at left
      simp [h]
      rw [← left]

      simp at h
      rw [h] at left
      simp [h]
      rw [← left]

@[simp]
lemma iff_false (ϕ ψ : Fml α) (v : Val α) :
    ⟦ϕ ↔ ψ , v⟧ = false ↔ ((⟦ϕ , v⟧ = true) ↔ (⟦ψ , v⟧ = false)) := by
      constructor
      intro h
      constructor
      intro h_links
      simp [Fml.iff] at h
      simp [h_links] at h
      trivial
      simp [Fml.iff] at h
      intro links
      simp [links] at h
      assumption

      simp
      intro h
      simp [Fml.iff]
      by_cases ht : ⟦ϕ , v⟧ = true
      left
      rw [ht] at h
      simp [*] at h
      constructor
      trivial
      trivial

      simp [h]

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
      | @cons ψ Γ' ih => simp [ih]

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
      | @cons ψ Γ' ih => simp [ih]

@[simp]
lemma big_conj_finset_false (Γ : Finset (Fml α)) (v : Val α) :
    ⟦⋀ Γ , v⟧ = false ↔ ∃ ϕ ∈ Γ, ⟦ϕ , v⟧ = false := by
      unfold Fml.big_conj_finset
      simp
end Val


def Sat {α : Type u } (Γ : Set (Fml α)) : Prop :=
  ∃ v : Val α, (∀ψ ∈ Γ, ⟦ψ , v⟧ = true)

namespace Sat

variable { α : Type u}

@[simp]
lemma truth_monotone {v : Val α } {Γ Δ : Set (Fml α )} (h : Γ ⊆ Δ) (g : ∀ψ ∈  Δ, ⟦ψ , v ⟧ = true) :
    ∀ψ ∈  Γ, ⟦ψ , v ⟧ = true := by
      intro ψ hψ
      apply g
      apply h hψ

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

-- # Logical Consequence

def Consequence { α : Type u} (Γ : Set (Fml α)) (ϕ : Fml α) : Prop :=
  ∀ v : Val α, (∀ ψ ∈ Γ, ⟦ψ , v⟧ = true) → (⟦ϕ , v⟧ = true)

notation Γ " ⊨ " ϕ => Consequence Γ ϕ
notation Γ " ⊭ " ϕ => ¬ Consequence Γ ϕ

namespace Consequence

variable { α : Type u}

@[simp]
lemma def_iff {Γ : Set (Fml α)} {ϕ : Fml α} :
    (Γ ⊨ ϕ) ↔ (∀ v : Val α, (∀ ψ ∈ Γ, ⟦ψ , v⟧ = true) → (⟦ϕ , v⟧ = true)) := by
  rfl

@[simp]
lemma consequence_iff_not_sat {Γ : Set (Fml α)} :
  ∀ ϕ : Fml α, (Γ ⊨ ϕ) ↔ ¬ Sat (Γ ∪ {¬ϕ}) := by
  intro ϕ
  unfold Sat Consequence
  constructor
  intro Γ' Sat
  rcases Sat with ⟨v, h⟩
  have hypothesis : ∀ ψ ∈ Γ, ⟦ψ, v⟧ = true := by
   intro ψ hψ
   apply h
   simp [hψ]
  have hϕ : ⟦ϕ, v⟧ = true := Γ' v hypothesis
  have hϕ_not : ⟦¬ϕ, v⟧ = true := by
   apply h
   simp
  simp [hϕ] at hϕ_not

  intro Sat v Γ'
  by_contra h
  apply Sat
  use v
  intro ψ h_ψ
  rcases h_ψ with ψ_in_Γ | rfl
  exact Γ' ψ ψ_in_Γ
  simp [h]

@[simp]
lemma non_consequence_iff_sat {Γ : Set (Fml α)} (ϕ : Fml α) :
  (Γ ⊭ ϕ) ↔ Sat (Γ ∪ {¬ϕ}) := by
  unfold Sat Consequence
  constructor
  intro not_Γ_to_Sat
  simp at not_Γ_to_Sat
  rcases not_Γ_to_Sat with ⟨v, h_Γ, h_ϕ_false⟩
  use v
  intro ψ hψ
  rcases hψ with h_in_Γ | rfl
  exact h_Γ ψ h_in_Γ
  simp [Val.neg_true]
  trivial

  intro Sat Con
  rcases Sat with ⟨v, h_sat⟩
  have h_Γ : ∀ ψ ∈ Γ, ⟦ψ , v⟧ = true := by
   intro ψ hψ
   apply h_sat
   simp [hψ]
  have h_ϕ_true : ⟦ϕ, v⟧ = true := Con v h_Γ
  have h_not_ϕ : ⟦¬ϕ, v⟧ = true := by
   apply h_sat
   simp
  simp [h_ϕ_true] at h_not_ϕ

@[simp]
lemma refl {Γ : Set (Fml α)} {ϕ : Fml α} (mem : ϕ ∈ Γ) : (Γ ⊨ ϕ) := by
  unfold Consequence
  intro v h_ψ
  apply h_ψ
  assumption

@[simp]
lemma monotonicity {Γ Δ : Set (Fml α)} {ϕ : Fml α}
    (h : Γ ⊨ ϕ) (g: Γ ⊆ Δ) : (Δ ⊨ ϕ) := by
    intro v h_Δ
    apply h v
    intro ψ hψ
    have hψ_in_Δ : ψ ∈ Δ := g hψ
    exact h_Δ ψ hψ_in_Δ

@[simp]
lemma trans {Γ Δ : Set (Fml α)} {ϕ : Fml α} (h : Γ ⊨ ϕ) (g : (Δ ∪ {ϕ}) ⊨ ϕ) : ((Γ ∪ Δ) ⊨ ϕ) := by
  intro v h_ψ
  apply h v
  intro ψ hψ
  apply h_ψ
  simp [hψ]

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

-- hψ : ∀ ψ ∈ Γ ∪ Δ ∪ Ξ, ⟦ψ , v⟧ = true
-- h : ∀ (v : Val α), (∀ ψ ∈ Γ, ⟦ψ , v⟧ = true) → ⟦ϕ , v⟧ = true ∨ ⟦ψ , v⟧ = true
-- g : ∀ (v : Val α), ⟦ϕ , v⟧ = true → (∀ a ∈ Δ, ⟦a , v⟧ = true) → ⟦χ , v⟧ = true
-- f : ∀ (v : Val α), ⟦ψ , v⟧ = true → (∀ a ∈ Ξ, ⟦a , v⟧ = true) → ⟦χ , v⟧ = true

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


def Valid {α : Type u } (ϕ : Fml α) : Prop :=
  ∅ ⊨ ϕ

notation "⊨ " ϕ => Valid ϕ

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
      intro hψ v
      by_cases h : ∀ ψ ∈ Γ, ⟦ψ , v⟧ = true
      right
      exact hψ v h
      left
      push_neg at h
      simp at h
      trivial

end Valid


def Eqv {α : Type u} (ϕ ψ : Fml α) : Prop :=
  ⊨ (ϕ ↔ ψ)

notation ϕ " ⟚ " ψ => Eqv ϕ ψ

namespace Eqv

variable {α : Type u}

@[simp]
lemma equivalence_to_implication (ϕ ψ : Fml α) :
    (ϕ ⟚ ψ) ↔ (⊨ (ϕ → ψ)) ∧ (⊨ (ψ → ϕ)) := by
    simp
    constructor
    intro h
    constructor
    intro v
    simp [Eqv, Valid.valid_iff, Fml.iff] at h
    simp [h]

    intro v
    simp [Eqv, Valid.valid_iff, Fml.iff] at h
    simp [h]

    intro v
    simp [Eqv, Valid.valid_iff, Fml.iff]
    simp [v]

@[simp]
lemma refl (ϕ : Fml α) : ϕ ⟚ ϕ := by
  simp[Eqv]

@[simp]
lemma symm {ϕ ψ : Fml α} (h : ϕ ⟚ ψ) : ψ ⟚ ϕ := by
  simp[Eqv] at h
  simp[Eqv]
  intro v
  rw [h v]

@[simp]
lemma iff_negation {ϕ ψ : Fml α} (h : ϕ ⟚ ψ) : (¬ϕ) ⟚ (¬ψ) := by
  simp[Eqv] at h
  simp[Eqv]
  intro v
  rw [h v]

@[simp]
lemma iff_conjunction {ϕ₁ ϕ₂ ψ₁ ψ₂ : Fml α}
  (h₁ : ϕ₁ ⟚ ψ₁) (h₂ : ϕ₂ ⟚ ψ₂) : (ϕ₁ ∧ ϕ₂) ⟚ (ψ₁ ∧ ψ₂) := by
  intro v h
  simp
  simp [Eqv] at h₁
  simp [Eqv] at h₂
  constructor
  intro h_h₁
  simp [h₁] at h_h₁
  simp [h₂] at h_h₁
  assumption

  intro h1
  rw [h₁ v]
  rw [h₂ v]
  assumption

end Eqv
