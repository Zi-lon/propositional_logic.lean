import PropositionalLogic.Syntax
import PropositionalLogic.Semantics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lemmas

open Fml
open Classical

universe u

variable {α : Type u} 

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

def cut {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α} (der_left : Der Γ ϕ ) (der_right : Der (Δ ∪ {ϕ}) ψ) :
    Der (Γ ∪ Δ) ψ := by
    let der_right' : Der Δ (ϕ → ψ) := by
      apply Der.imp_intro
      exact der_right
    rw[Set.union_comm] 
    exact Der.imp_elim der_right' der_left


lemma derivations_are_finite {Γ : Set (Fml α)} {ϕ : Fml α} (d : Der Γ ϕ) : Set.Finite Γ := by
  induction d with
  | ass => 
      apply Set.finite_singleton
  | weak d ih => 
      apply Set.Finite.union  
      · trivial
      · simp
  | neg_intro d ih => 
      simp at ih
      trivial
  | imp_elim d d'
  | neg_elim d d'
  | conj_intro d d' => 
      apply Set.Finite.union  
      trivial
      trivial
  | bot_elim d 
  | conj_elim_left d 
  | conj_elim_right d 
  | disj_intro_left d 
  | disj_intro_right d => trivial
  | imp_intro d => 
    simp at *
    trivial
  | disj_elim d d' d'' ih₁ ih₂ ih₃ => 
    simp at ih₁ ih₂ ih₃
    apply Set.Finite.union 
    apply Set.Finite.union ih₁ ih₂
    exact ih₃
  | raa d ih => 
      simp at ih
      trivial

def provable {α : Type u} (Γ : Set (Fml α)) (ϕ : Fml α) : Prop :=
  ∃ Δ : Set (Fml α), Δ ⊆ Γ ∧ Nonempty (Der Δ ϕ)

notation Γ " ⊢ " ϕ => provable Γ ϕ
notation Γ " ⊬ " ϕ => ¬(provable Γ ϕ)

@[simp]
lemma ass_provable {ϕ : Fml α} :
    {ϕ} ⊢ ϕ := 
      ⟨{ϕ}, subset_refl {ϕ}, Nonempty.intro Der.ass⟩

@[simp]
lemma weak_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ ϕ) :
    (Γ ∪ {ψ}) ⊢  ϕ := by
      sorry

@[simp]
lemma raa_provable {Γ : Set (Fml α)} {ϕ : Fml α} (h :(Γ ∪ {¬ϕ}) ⊢  ⊥ ) : 
    (Γ ⊢ ϕ) := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      by_cases g : Δ ⊆ Γ
      · have der_phi : Der Δ ϕ := by
          apply Der.bot_elim der
        exact ⟨Δ, g, Nonempty.intro der_phi⟩ 
      · have neg_phi_in_delta : (¬ϕ) ∈ Δ := by
          simp at h_sub g
          grind
        let Δ' := Δ\{¬ϕ}
        have f : Δ' ⊆ Γ := by
           grind
        have aux: (Δ' ∪ {¬ϕ}) = Δ := by
          simp[Δ']
          grind
        have der_phi : Der (Δ' ∪ {¬ϕ}) ⊥ := by
          rewrite [←aux] at der
          apply Der.bot_elim der
        have der_fin : Der Δ' ϕ := by
          apply Der.raa der_phi
        exact ⟨Δ', f, Nonempty.intro der_fin⟩

lemma neg_intro_provable {Γ : Set (Fml α)} {ϕ : Fml α} (h : (Γ ∪ {ϕ}) ⊢ ⊥) :
    Γ ⊢ ¬ϕ := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      by_cases g : Δ ⊆ Γ
      · have delta_proves_neg_phi : Der Δ (¬ϕ) := by
          apply Der.bot_elim der
        exact ⟨Δ, g, Nonempty.intro delta_proves_neg_phi⟩
      · have phi_in_delta : ϕ ∈ Δ := by
          simp at h_sub g
          grind
        let Δ' := Δ\{ϕ}
        have aux: (Δ' ∪ {ϕ}) = Δ := by
          simp[Δ']
          grind
        have f : Δ' ⊆ Γ := by
           grind
        have der_phi : Der (Δ' ∪ {ϕ}) ⊥ := by
          rewrite [←aux] at der
          apply Der.bot_elim der
        have der_fin : Der Δ' (¬ϕ) := by
          apply Der.neg_intro der_phi
        exact ⟨Δ', f, Nonempty.intro der_fin⟩

lemma neg_elim_provable {Γ Δ : Set (Fml α)} {ϕ : Fml α} (h1 : Γ ⊢ ϕ) (h2 : Δ ⊢ ¬ϕ) :
    (Γ ∪ Δ) ⊢ ⊥ := by
      let ⟨Γ', h_sub1, h_der1⟩ := h1
      let der1 := Classical.choice h_der1
      let ⟨Δ', h_sub2, h_der2⟩ := h2
      let der2 := Classical.choice h_der2
      have der_bot : Der (Γ' ∪ Δ') ⊥ := by
        apply Der.neg_elim der1 der2
      have big_sub : (Γ' ∪  Δ') ⊆ (Γ ∪ Δ) := by
        simp
        apply And.intro
        apply Set.subset_union_of_subset_left h_sub1
        apply Set.subset_union_of_subset_right h_sub2
      exact ⟨(Γ' ∪ Δ'), big_sub, Nonempty.intro der_bot⟩

lemma rfl_provable {Γ : Set (Fml α)} {ϕ : Fml α} (h : ϕ ∈ Γ) :
    Γ ⊢ ϕ := by
      simp only [provable]
      have h_sub : {ϕ} ⊆ Γ := by
          simp
          exact h
      apply Exists.intro {ϕ}
      apply And.intro h_sub
      exact Nonempty.intro Der.ass

lemma conj_elim_left_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ (ϕ ∧ ψ)) :
    Γ ⊢ ϕ := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      have der_phi : Der Δ ϕ := by
        apply Der.conj_elim_left der
      exact ⟨Δ, h_sub, Nonempty.intro der_phi⟩

-- lemma conj_elim_left_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ (ϕ ∧ ψ)) :
--     Γ ⊢ ϕ := by
--       let ⟨Δ, h_sub, h_der⟩ := h
--       let der := Classical.choice h_der
--       have der_phi : Der Δ ϕ := by
--         apply Der.conj_elim_left der
--       exact ⟨Δ, h_sub, Nonempty.intro der_phi⟩

lemma conj_elim_right_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ (ϕ ∧ ψ)) :
    Γ ⊢ ψ := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      have der_psi : Der Δ ψ := by
        apply Der.conj_elim_right der
      exact ⟨Δ, h_sub, Nonempty.intro der_psi⟩


lemma disj_intro_left_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ ϕ) :
    Γ ⊢ (ϕ ∨ ψ) := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      -- let der_disj := (@Der.disj_intro_left Δ \psider 
      exact ⟨Δ, h_sub, Nonempty.intro (Der.disj_intro_left der)⟩

lemma disj_intro_right_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ ψ) :
    Γ ⊢ (ϕ ∨ ψ) := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      exact ⟨Δ, h_sub, Nonempty.intro (Der.disj_intro_right der)⟩

lemma disj_syll_provable {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α} (h1 : Γ ⊢  ϕ ∨ ψ) (h2 : Δ ⊢ ¬ϕ) :
    (Γ ∪ Δ) ⊢ ψ := by
      let ⟨Γ', h_sub1, h_der1⟩ := h1
      let der1 := Classical.choice h_der1
      let ⟨Δ', h_sub2, h_der2⟩ := h2
      let der2 := Classical.choice h_der2
      have der3 : Der ({ϕ} ∪ Δ') ψ := by
        have rfl_der : Der {ϕ} ϕ := by
          apply Der.ass
        apply Der.bot_elim
        apply Der.neg_elim rfl_der der2
      rw[←Set.union_comm] at der3
      have rfl_der2 : Der {ψ} ψ := by
        apply Der.ass
      have der_psi : Der (Γ' ∪ Δ' ∪ ∅) ψ := by
        apply Der.disj_elim der1
        exact der3  
        simp 
        exact rfl_der2
      simp at der_psi
      have big_sub : (Γ' ∪  Δ') ⊆ (Γ ∪ Δ) := by
        simp
        apply And.intro
        apply Set.subset_union_of_subset_left h_sub1
        apply Set.subset_union_of_subset_right h_sub2
      exact ⟨(Γ' ∪ Δ'), big_sub, Nonempty.intro der_psi⟩

lemma conj_intro_provable {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α} (h1 : Γ ⊢ ϕ) (h2 : Δ ⊢ ψ) :
    (Γ ∪ Δ) ⊢ (ϕ ∧ ψ) := by
      let ⟨Γ', h_sub1, h_der1⟩ := h1
      let der1 := Classical.choice h_der1
      let ⟨Δ', h_sub2, h_der2⟩ := h2
      let der2 := Classical.choice h_der2
      let der := Der.conj_intro der1 der2
      have big_sub : (Γ' ∪  Δ') ⊆ (Γ ∪ Δ) := by
        simp
        apply And.intro
        apply Set.subset_union_of_subset_left h_sub1
        apply Set.subset_union_of_subset_right h_sub2
      exact ⟨(Γ' ∪ Δ'), big_sub, Nonempty.intro der⟩

lemma vacuous_implication_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ ¬ϕ) :
    Γ ⊢ ϕ → ψ := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      have rfl_der : Der {ϕ} ϕ := by
        apply Der.ass
      have derive_bot: Der ({ϕ} ∪ Δ) ⊥ := by
        apply Der.neg_elim rfl_der
        apply der
      rw[Set.union_comm]  at derive_bot
      have der_imp : Der Δ (ϕ → ψ) := by
        apply Der.imp_intro
        apply Der.bot_elim derive_bot
      exact ⟨Δ, h_sub, Nonempty.intro der_imp⟩

lemma consequent_to_impl_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ ψ) :
    Γ ⊢ ϕ → ψ := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      have der_phi : Der (Δ ∪ {ϕ}) ψ := by
        apply Der.weak der
      have der_final : Der Δ (ϕ → ψ) := by
        apply Der.imp_intro der_phi
      exact ⟨Δ, h_sub, Nonempty.intro der_final⟩

lemma imp_intro_provable {Γ : Set (Fml α)} {ϕ ψ : Fml α} (h : (Γ ∪ {ϕ}) ⊢ ψ) :
    Γ ⊢ (ϕ → ψ) := by
      let ⟨Δ, h_sub, h_der⟩ := h
      let der := Classical.choice h_der
      let Δ' := Δ \ {ϕ}
      have g : Δ' ⊆ Γ := by
         grind
      by_cases f : ϕ ∈ Δ
      · have h_eq : Δ = (Δ' ∪ {ϕ}) := by
          simp[Δ']
          grind
        simp only [h_eq] at der
        have der_imp : Der Δ' (ϕ → ψ) := by 
          apply Der.imp_intro der
        exact ⟨Δ', g, Nonempty.intro der_imp⟩
      · have h_eq : Δ = Δ' := by
          simp[Δ']
          grind
        have der_phi : Der (Δ ∪ {ϕ}) ψ := by
         apply Der.weak der
        have der_final : Der Δ (ϕ → ψ) := by
         apply Der.imp_intro der_phi
        sorry 
        -- exact ⟨Δ, h_sub, Nonempty.intro der_final⟩
        
lemma imp_elim_provable {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α} (h1 : Γ ⊢ (ϕ → ψ)) (h2 : Δ ⊢ ϕ) :
    (Γ ∪ Δ) ⊢ ψ := by
      let ⟨Γ', h_sub1, h_der1⟩ := h1
      let der1 := Classical.choice h_der1
      let ⟨Δ', h_sub2, h_der2⟩ := h2
      let der2 := Classical.choice h_der2
      let der := Der.imp_elim der1 der2
      have big_sub : (Γ' ∪  Δ') ⊆ (Γ ∪ Δ) := by
        simp
        apply And.intro
        apply Set.subset_union_of_subset_left h_sub1
        apply Set.subset_union_of_subset_right h_sub2
      exact ⟨(Γ' ∪ Δ'), big_sub, Nonempty.intro der⟩


lemma cut_derivable {Γ Δ : Set (Fml α)} {ϕ ψ : Fml α} (h : Γ ⊢ ϕ ) (g : (Δ ∪ {ϕ}) ⊢ ψ) :
    (Γ ∪ Δ) ⊢ ψ := by
      sorry


namespace Der

variable {α : Type u}

def height {Γ : Set (Fml α)} {ϕ : Fml α} : Der Γ ϕ → Nat 
 | ass => 0
 | disj_elim d d' d'' => max (max (height d) (height d')) (height d'') + 1
 | imp_elim d d'
 | neg_elim d d' 
 | conj_intro d d' => max (height d) (height d') + 1
 | weak d 
 | imp_intro d
 | bot_elim d 
 | neg_intro d 
 | conj_elim_left d 
 | conj_elim_right d 
 | disj_intro_left d 
 | disj_intro_right d => (height d) + 1 
 | raa d => (height d) + 1 

def lh {Γ Δ: Set (Fml α)} {ϕ ψ : Fml α} : Der Γ ϕ → Der Δ ψ → Prop := by
   intro d d'
   let t := height d < height d'
   exact t

-- lemma wf_lh (Γ Δ: Set (Fml α)) (ϕ ψ : Fml α) : WellFounded (lh : (Der Γ ϕ) → (Der Δ ψ) → Prop) := by
--   simpa [lh] using
--     (measure height).wf
--
-- def induct_on_cxty {P : Fml α → Prop} (φ : Fml α)
--   (h : ∀ ψ, (∀ χ, cxty χ < cxty ψ → P χ) → P ψ) : P φ :=
--   WellFounded.induction wf_lc φ h

end Der

lemma soundness_der (Γ : Set (Fml α)) (ϕ : Fml α) :
    (Der Γ ϕ) → (Γ ⊨ ϕ) := by
    intro d
    induction d with
      | ass => simp
      | weak =>
        apply Consequence.monotonicity
        trivial
        simp
      | bot_elim => 
          apply Consequence.bot_elim
          trivial
      | neg_intro => 
          apply Consequence.neg_intro
          trivial
      | neg_elim => 
          apply Consequence.neg_elim
          trivial
          trivial
      | conj_intro =>
        apply Consequence.conj_intro
        trivial
        trivial
      | conj_elim_left =>
        apply Consequence.conj_elim_left
        trivial
      | conj_elim_right =>
        apply Consequence.conj_elim_right
        trivial
      | disj_intro_left =>
        apply Consequence.disj_intro_left
        trivial
      | disj_intro_right=>
        apply Consequence.disj_intro_right
        trivial
      | disj_elim =>
        apply Consequence.disj_elim
        trivial
        trivial
        trivial
      | imp_intro =>
        apply Consequence.imp_intro
        trivial
      | imp_elim => 
        apply Consequence.imp_elim
        trivial
        trivial
      | raa =>
        apply Consequence.raa
        trivial

theorem soundness {α : Type u} (Γ : Set (Fml α)) (ϕ : Fml α) :
    (Γ ⊢ ϕ) → (Γ ⊨ ϕ) := by
    intro h_prov
    let ⟨Δ, h_sub, h_ned⟩ := h_prov
    apply Consequence.monotonicity 
    apply soundness_der Δ ϕ (Classical.choice h_ned)
    apply h_sub

def consistent {α : Type u} (Γ : Set (Fml α)) : Prop :=
    Γ ⊬ ⊥

@[simp]
lemma consistent_iff_not_provable_everything {α : Type u} (Γ : Set (Fml α)) :
    (consistent Γ) ↔ ∃ ϕ : Fml α, Γ ⊬ ϕ :=
  by
    apply Iff.intro
    · intro h_con
      simp[consistent] at h_con
      apply Exists.intro (⊥ : Fml α) h_con
    · intro h_ex
      by_contra h_inco
      rw[consistent] at h_inco
      simp at h_inco
      apply Exists.elim h_ex
      intro ψ h_notprov
      let ⟨Δ, h_sub, h_der⟩ := h_inco
      let der := Classical.choice h_der
      have der_psi : Der Δ ψ := by
         apply Der.bot_elim der 
      have prove_psi : Γ ⊢ ψ := by
        apply Exists.intro Δ
        apply And.intro h_sub
        apply Nonempty.intro der_psi
      apply h_notprov prove_psi


-- @[simp]
lemma consistent_iff_not_provable_contradiction {α : Type u} (Γ : Set (Fml α)) :
    (consistent Γ) ↔ ¬ ∃ ϕ : Fml α, (Γ ⊢ ϕ) ∧ (Γ ⊢ ¬ϕ) := by
  apply Iff.intro
  · intro h_con h_ex
    apply Exists.elim h_ex
    intro ψ h
    let ⟨Δ, h_sub_delta, der1⟩ := h.left
    let ⟨Ξ, h_sub_xi, der2⟩ := h.right
    let der_phi := Classical.choice der1
    let der_neg_phi := Classical.choice der2
    let der_bot := by apply Der.neg_elim der_phi der_neg_phi
    rw[consistent] at h_con
    have gamma_proves_bot : Γ ⊢ ⊥ := by
      apply Exists.intro (Δ ∪ Ξ)
      apply And.intro
      · apply Set.union_subset h_sub_delta h_sub_xi
      · apply Nonempty.intro
        exact der_bot
    apply h_con gamma_proves_bot
  · intro h h_incon
    let ⟨Δ, h_sub, der⟩ := h_incon
    let der := Classical.choice der 
    have provable_bot : Γ ⊢ ⊥ := ⟨Δ, h_sub, Nonempty.intro der⟩
    have provable_top : Γ ⊢ ¬⊥ := ⟨Δ, h_sub, Nonempty.intro (Der.bot_elim der)⟩
    have conj : (Γ ⊢ ⊥) ∧ (Γ ⊢ ¬⊥) := by
      apply And.intro provable_bot provable_top
    apply h
    exact ⟨⊥, provable_bot, provable_top⟩ 
    
theorem if_sat_then_consistent {α : Type u} (Γ : Set (Fml α)) :
    Sat Γ → consistent Γ :=
  by
    intro h_sat h_incon
    rw[Sat] at h_sat
    let ⟨v, hv⟩ := h_sat
    have gamma_implies_bot : Γ ⊨ ⊥ := by
      apply soundness Γ ⊥ h_incon
    have bot_true : ⟦⊥ , v⟧ = true := by
      apply gamma_implies_bot v hv
    rw[Val.eval] at bot_true
    apply Bool.noConfusion bot_true

lemma if_negation_inconsistent_then_provable (Γ : Set (Fml α)) (ϕ : Fml α) :
    ¬ consistent (Γ ∪ {¬ϕ}) → (Γ ⊢ ϕ) :=
  by
    intro h_incon
    simp only [consistent, not_not] at h_incon
    apply raa_provable h_incon

 lemma if_inconsistent_then_provable (Γ : Set (Fml α)) (ϕ : Fml α) :
    ¬ consistent (Γ ∪ {ϕ}) → (Γ ⊢ ¬ϕ) :=
  by
    intro h_incon
    rw[consistent] at h_incon
    simp only [not_not] at h_incon
    apply neg_intro_provable h_incon


lemma subseteq_consistent {α : Type u} {Γ Δ : Set (Fml α)} (h_sub : Γ ⊆ Δ) :
    consistent Δ → consistent Γ :=
  by
    intro h_contra h_incon
    let ⟨Ξ, h_sub_xi, h_der⟩ := h_incon
    let der := Classical.choice h_der
    have h_xi_subset_delta : Ξ ⊆ Δ := by
      grind
    let delta_implies_bot : Δ ⊢ ⊥ := 
      ⟨Ξ, (h_xi_subset_delta), Nonempty.intro der⟩
    apply h_contra delta_implies_bot

lemma subseteq_inconsistent {α : Type u} {Γ Δ : Set (Fml α)} (h_sub : Γ ⊆ Δ) :
    ¬ consistent Γ → ¬ consistent Δ :=
  by
    apply mt 
    apply subseteq_consistent h_sub

def maximally_consistent (Γ : Set (Fml α)) : Prop :=
  consistent Γ ∧ ∀ Δ : Set (Fml α), (Γ ⊂ Δ) → ¬ consistent Δ

variable [Nonempty α] [Countable α]

def chain (Γ : Set (Fml α)) : ℕ → Set (Fml α) 
  | .zero => Γ
  | .succ n => 
    if consistent ((chain Γ n) ∪ {Countable.numbering n}) then 
       ((chain Γ n) ∪ {Countable.numbering n}) 
    else 
      (chain Γ n)

def max_extension (Γ : Set (Fml α)) : Set (Fml α) :=
  ⋃ n : ℕ , chain Γ n 

lemma chain_monotone (Γ : Set (Fml α)) (n : ℕ) :
    chain Γ n ⊆ chain Γ (n + 1) := by
  simp only [chain]
  grind

lemma chain_mono_le (Γ : Set (Fml α)) {m n : ℕ} (hmn : m ≤ n) :
    chain Γ m ⊆ chain Γ n := by
    induction hmn with
    | refl => rfl
    | step h_le ih => 
      simp only [chain]
      grind

lemma gamma_subseteq_max_extension (Γ : Set (Fml α)) :
    Γ ⊆ max_extension Γ := by
  intro ϕ h_in
  simp [max_extension]
  have phi_in_chain_zero : ϕ ∈ chain Γ 0 := by
    simp [chain]
    exact h_in
  exact ⟨0, phi_in_chain_zero⟩
  
lemma chain_consistent (Γ : Set (Fml α)) (n : ℕ) (h_cons : consistent Γ) :
    consistent (chain Γ n) := by
  induction n with
  | zero => exact h_cons
  | succ n ih =>
      by_cases h_n_cons : consistent ((chain Γ n) ∪ {Countable.numbering n})
      · simp only [chain, h_n_cons]
        exact h_n_cons
      · simp only [chain, h_n_cons]
        exact ih

lemma max_extension_consistent {Γ : Set (Fml α)} (h : consistent Γ) :
    consistent (max_extension Γ) := by
  classical
  by_contra h_incon
  simp [consistent] at h_incon
  let ⟨Δ, h_sub, h_der⟩ := h_incon
  have hIndexExists : ∀ ϕ ∈  Δ, ∃ n : ℕ , ϕ ∈ chain Γ n := by
    intro ϕ h_in_delta
    simp [max_extension] at h_sub
    have phi_in_max : ϕ ∈ ⋃ n : ℕ , chain Γ n := by
      apply h_sub h_in_delta
    simp at phi_in_max 
    assumption
  have delta_finite : Set.Finite Δ :=
    derivations_are_finite (Classical.choice h_der)
  let ind : Fml α → ℕ := fun ϕ =>
    if hϕ : ϕ ∈ Δ then Nat.find (hIndexExists ϕ hϕ) else 0
  have ind_spec {ϕ : Fml α} (hϕ : ϕ ∈ Δ) :
      ϕ ∈ chain Γ (ind ϕ) := by
    have := Nat.find_spec (hIndexExists ϕ hϕ)
    simpa [ind, hϕ] using this
  obtain ⟨φ₀, h_bound⟩ :=
    Set.exists_upper_bound_image (s := Δ) (f := ind) delta_finite
  let k : ℕ := ind φ₀
  have delta_subset_chain_k : Δ ⊆ chain Γ k := by
    intro ϕ hϕ
    have h_le : ind ϕ ≤ k := by
      have := h_bound ϕ hϕ
      simpa [k] using this
    have h_in_chain_ind : ϕ ∈ chain Γ (ind ϕ) := ind_spec hϕ
    have h_sub_chain : chain Γ (ind ϕ) ⊆ chain Γ k :=
      chain_mono_le Γ h_le
    exact h_sub_chain h_in_chain_ind
  have chain_cons : consistent (chain Γ k) :=
    chain_consistent Γ k h
  have delta_consistent : consistent Δ :=
    subseteq_consistent (Γ := Δ) (Δ := chain Γ k) delta_subset_chain_k chain_cons
  have provable_bot : Δ ⊢ ⊥ :=
    ⟨Δ, subset_rfl, h_der⟩
  exact delta_consistent provable_bot

lemma max_extension_is_maximally_consistent {Γ : Set (Fml α)} (h : consistent Γ) :
    maximally_consistent (max_extension Γ) := by
  apply And.intro
  · apply max_extension_consistent h
  · intro Δ h_sub
    by_contra h_cons
    simp [max_extension] at h_sub
    have exists_phi : ∃ ϕ : Fml α, ϕ ∈ Δ ∧ ϕ ∉ max_extension Γ := by
      simp only [Set.ssubset_def] at h_sub
      grind
    let ⟨ϕ , h_in_delta, h_notin_max⟩ := exists_phi
    let i := Countable.index ϕ
    have aux2 : ϕ = Countable.numbering i := by
      simp[i]
    have cons : ¬consistent ((chain Γ i) ∪ {ϕ}) := by
      by_contra g
      have phi_in_nxt_chain : ϕ ∈ chain Γ (i + 1) := by
        unfold chain
        simp only [aux2] at g
        grind
      have phi_in_max : ϕ ∈ max_extension Γ := by
        simp [max_extension]
        exact ⟨i + 1, phi_in_nxt_chain⟩
      apply h_notin_max phi_in_max
    have sub_chain : ((chain Γ i) ∪ {ϕ}) ⊆ Δ := by
      apply Set.union_subset 
      simp[Set.ssubset_def] at h_sub
      exact h_sub.1 i 
      simp only [Set.singleton_subset_iff]
      exact h_in_delta
    apply subseteq_inconsistent sub_chain cons
    exact h_cons

lemma maxcon_closure {Γ : Set (Fml α)} {ϕ  : Fml α} 
  (h : maximally_consistent Γ) (g : Γ ⊢  ϕ) :
    ϕ ∈ Γ := by
      by_contra h_notin
      have incon : ¬ consistent (Γ ∪ {ϕ}) := by
        apply h.right
        simp [Set.ssubset_def]
        grind
      have provable_neg_phi : Γ ⊢ ¬ϕ :=
        if_inconsistent_then_provable Γ ϕ incon
      have gamma_proves_bot : Γ ⊢ ⊥ := by
        rw[←Set.union_self Γ]
        apply neg_elim_provable g provable_neg_phi 
      apply h.1 gamma_proves_bot

lemma max_con_bivalence {Γ : Set (Fml α)} (h : maximally_consistent Γ) (ϕ : Fml α) :
    (ϕ ∈ Γ) ∨ ((¬ϕ) ∈ Γ) := by
      let Γ' := Γ ∪ {ϕ}
      by_cases g : consistent Γ' 
      · have phi_in_gamma : ϕ ∈ Γ := by
          by_contra
          have gamma_ssubseteq : Γ ⊂ Γ' := by
            simp [Set.ssubset_def]
            grind
          unfold maximally_consistent at h
          apply h.2 Γ' gamma_ssubseteq
          exact g
        apply Or.inl phi_in_gamma
      · have gamma_proves_neg_phi : Γ ⊢ ¬ϕ :=
          if_inconsistent_then_provable Γ ϕ g
        have neg_phi_in_gamma : (¬ϕ) ∈ Γ :=
          maxcon_closure h gamma_proves_neg_phi
        apply Or.inr neg_phi_in_gamma

lemma max_con_no_contradictions {Γ : Set (Fml α)} (h : maximally_consistent Γ) (ϕ : Fml α) :
    ¬ ((ϕ ∈ Γ) ∧ ((¬ϕ) ∈ Γ)) := by
      by_contra h_contr
      have gamma_proves_phi : Γ ⊢ ϕ := 
        have h_sub : {ϕ} ⊆ Γ := by
          simp
          exact h_contr.1
        ⟨{ϕ}, h_sub , Nonempty.intro Der.ass⟩
      have gamma_proves_neg_phi : Γ ⊢ ¬ϕ :=
        have h_sub : {¬ϕ} ⊆ Γ := by
          simp
          exact h_contr.2
        ⟨{¬ϕ}, h_sub , Nonempty.intro Der.ass⟩
      apply h.1
      rw[←Set.union_self Γ]
      apply neg_elim_provable gamma_proves_phi gamma_proves_neg_phi

@[simp]
lemma max_con_iff {Γ : Set (Fml α)} (h : maximally_consistent Γ) (ϕ : Fml α) :
    (ϕ ∈ Γ) ↔  ((¬ϕ) ∉ Γ) := by
  constructor
  · intro hϕ hneg
    exact max_con_no_contradictions (Γ := Γ) h ϕ ⟨hϕ, hneg⟩
  · intro hnot
    have hb := max_con_bivalence (Γ := Γ) h ϕ
    cases hb with
    | inl hϕ => exact hϕ
    | inr hneg => exact (hnot hneg).elim

@[simp]
lemma max_con_iff_neg {Γ : Set (Fml α)} (h : maximally_consistent Γ) (ϕ : Fml α) :
    ((¬ϕ) ∈ Γ) ↔  (ϕ ∉ Γ) := by
  constructor
  · intro g hneg
    apply max_con_no_contradictions (Γ := Γ) h ϕ
    apply And.intro hneg g
  · intro g 
    have max_con_iff := max_con_iff (Γ := Γ) h ϕ
    rw[←not_iff_not] at max_con_iff
    simp at max_con_iff
    grind

@[simp]
lemma max_con_contains_or {Γ : Set (Fml α)} (h : maximally_consistent Γ) {ϕ ψ : Fml α} :
    ((ϕ ∨ ψ) ∈ Γ) ↔ (ϕ ∈ Γ ∨ ψ ∈ Γ) := by
      apply Iff.intro
      · intro f
        by_cases g : ϕ ∈ Γ
        · exact Or.inl g
        · have gamma_proves_or : Γ ⊢ (ϕ ∨ ψ) := by
            apply rfl_provable f
          have neg_phi_in_gamma : (¬ϕ) ∈ Γ := by
            apply Or.resolve_left (max_con_bivalence h ϕ) g
          have gamma_proves_neg_phi : Γ ⊢ ¬ϕ := by
            apply rfl_provable neg_phi_in_gamma
          have proves_psi : Γ ⊢ ψ := by
            rw[←Set.union_self Γ]
            apply disj_syll_provable gamma_proves_or gamma_proves_neg_phi
          have psi_in_gamma : ψ ∈ Γ := by
            apply maxcon_closure h proves_psi
          exact Or.inr psi_in_gamma
      · intro f
        cases f with
        | inl g =>
            have gamma_proves_phi : Γ ⊢ ϕ := by
              apply rfl_provable g
            have gamma_proves_or : Γ ⊢ (ϕ ∨ ψ) := by
              apply disj_intro_left_provable gamma_proves_phi
            exact maxcon_closure h gamma_proves_or
        | inr g =>
            have gamma_proves_psi : Γ ⊢ ψ := by
              apply rfl_provable g
            have gamma_proves_or : Γ ⊢ (ϕ ∨ ψ) := by
              apply disj_intro_right_provable gamma_proves_psi
              -- apply Consequence.disj_intro_right gamma_proves_psi
            exact maxcon_closure h gamma_proves_or

@[simp]
lemma max_con_contains_and {Γ : Set (Fml α)} (h : maximally_consistent Γ) {ϕ ψ : Fml α} :
    ((ϕ ∧ ψ) ∈ Γ) ↔ (ϕ ∈ Γ ∧ ψ ∈ Γ) := by
      apply Iff.intro
      · intro f
        have gamma_proves_and : Γ ⊢ (ϕ ∧ ψ) := by
          apply rfl_provable f
        have gamma_proves_phi : Γ ⊢ ϕ := by
          apply conj_elim_left_provable gamma_proves_and
        have phi_in_gamma : ϕ ∈ Γ := by
          apply maxcon_closure h gamma_proves_phi
        have gamma_proves_psi : Γ ⊢ ψ := by
          apply conj_elim_right_provable gamma_proves_and
        have psi_in_gamma : ψ ∈ Γ := by
          apply maxcon_closure h gamma_proves_psi
        exact And.intro phi_in_gamma psi_in_gamma
      · intro f
        have gamma_proves_phi : Γ ⊢ ϕ := by
          apply rfl_provable f.left
        have gamma_proves_psi : Γ ⊢ ψ := by
          apply rfl_provable f.right
        have gamma_proves_and : Γ ⊢ (ϕ ∧ ψ) := by
          rw[←Set.union_self Γ]
          apply conj_intro_provable gamma_proves_phi gamma_proves_psi
        exact maxcon_closure h gamma_proves_and

lemma max_con_contains_imp {Γ : Set (Fml α)} (h : maximally_consistent Γ) {ϕ ψ : Fml α} :
    ((ϕ → ψ) ∈ Γ) ↔ (ϕ ∈ Γ → ψ ∈ Γ) := by
      apply Iff.intro
      · intro f g 
        have f_1 : Γ ⊢ (ϕ → ψ) := by
          apply rfl_provable f
        have f_2 : Γ ⊢ ϕ := by
          apply rfl_provable g
        apply maxcon_closure h
        rw[←Set.union_self Γ]
        apply imp_elim_provable f_1 f_2
      · intro f
        by_cases g : ϕ ∈ Γ
        · have psi_in_gamma : ψ ∈ Γ := f g
          have gamma_proves_psi : Γ ⊢ ψ := by
            apply rfl_provable psi_in_gamma
          have gamma_proves_imp : Γ ⊢ (ϕ → ψ) := by
            apply consequent_to_impl_provable gamma_proves_psi
          exact maxcon_closure h gamma_proves_imp
        · have neg_phi_in_gamma : (¬ϕ) ∈ Γ := by
            apply Or.resolve_left (max_con_bivalence h ϕ) g
          have proves_neg_phi : Γ ⊢ ¬ϕ := by
            apply rfl_provable neg_phi_in_gamma
          have proves_imp : Γ ⊢ (ϕ → ψ) := by
            apply vacuous_implication_provable proves_neg_phi
          exact maxcon_closure h proves_imp

lemma max_con_bot_not_in {Γ : Set (Fml α)} (h : maximally_consistent Γ) :
    ⊥ ∉ Γ := by
      by_contra h_in
      have gamma_proves_bot : Γ ⊢ ⊥ := by
        apply rfl_provable h_in
      apply h.1 gamma_proves_bot

noncomputable def assoc_val (Γ : Set (Fml α))  : Val α :=
  fun a => if (Fml.var a) ∈ Γ then true else false

lemma model_existence_for_maxcon (Γ : Set (Fml α)) (h : maximally_consistent Γ) (ϕ : Fml α) :
    (ϕ ∈ Γ) ↔ (⟦ϕ , (assoc_val Γ) ⟧ = true) := by
      induction ϕ with
      | var a => 
          simp[Val.eval,assoc_val]
      | bot => 
          simp[Val.eval]
          exact max_con_bot_not_in h
      | neg ψ ih => 
          simp[Val.eval] at *
          have aux : (¬ψ) ∉ Γ ↔ ⟦ψ , assoc_val Γ⟧ = true := by
            rw[max_con_iff h ψ] at ih
            trivial
          grind
      | disj ψ θ ih₁ ih₂ => 
          simp[Val.eval] at *
          simp[max_con_contains_or h]
          grind
      | conj ψ θ ih₁ ih₂ => 
          simp[Val.eval] at *
          simp[max_con_contains_and h]
          grind

lemma model_existence {Γ : Set (Fml α)} (h : consistent Γ) (ϕ : Fml α) :
    ϕ ∈ Γ → ⟦ϕ , (assoc_val (max_extension Γ)) ⟧ = true := by
      intro h_in
      have maxcon := max_extension_is_maximally_consistent h
      have h_subset : Γ ⊆ max_extension Γ := 
        gamma_subseteq_max_extension Γ
      have phi_in_max : ϕ ∈ max_extension Γ := by
        apply h_subset h_in
      apply (model_existence_for_maxcon (max_extension Γ) maxcon ϕ).1 phi_in_max

lemma completeness_lemma {Γ : Set (Fml α)} {ϕ : Fml α} :
    (Γ ⊬ ϕ) → Sat (Γ ∪ {¬ϕ}) := by
      intro h
      have h_cons : consistent Γ := by
        simp
        apply Exists.intro ϕ h
      have h_cons' : consistent (Γ ∪ {¬ϕ}) := by
        let aux := if_negation_inconsistent_then_provable Γ ϕ
        let mt_aux := mt aux
        simp only [not_not] at mt_aux
        apply mt_aux h
      let extension := max_extension (Γ ∪ {¬ϕ})
      simp [Sat]
      let val := assoc_val extension
      have gammas_true : ∀ ψ ∈ Γ, ⟦ψ , val⟧ = true := by
        intro ψ h_in
        have h_sub : Γ ⊆ (Γ ∪ {¬ϕ}) := by
          simp
        have psi_in_extension : ψ ∈ extension := by
          simp only [extension] 
          apply gamma_subseteq_max_extension (Γ ∪ {¬ϕ})
          apply h_sub
          trivial
        apply model_existence h_cons' ψ
        apply h_sub h_in
      have phi_false : ⟦ϕ , val⟧ = false := by
        have neg_phi_in_extension : (¬ϕ) ∈ extension := by
          simp only [extension]
          apply gamma_subseteq_max_extension (Γ ∪ {¬ϕ})
          simp
        have neg_phi_true : ⟦¬ϕ , val⟧ = true := by
          let thing := model_existence_for_maxcon extension (max_extension_is_maximally_consistent h_cons') (¬ϕ)
          apply thing.1 neg_phi_in_extension
        simp[Val.eval] at neg_phi_true
        trivial
      apply Exists.intro val
      apply And.intro phi_false gammas_true

theorem completeness {Γ : Set (Fml α)} {ϕ : Fml α} :
    (Γ ⊨ ϕ) → (Γ ⊢ ϕ) := by
      intro h_sat
      by_contra h_notprov
      have sat := completeness_lemma h_notprov
      have my_lemma := ((@Consequence.non_consequence_iff_sat α Γ) ϕ).2
      apply my_lemma sat
      exact h_sat
