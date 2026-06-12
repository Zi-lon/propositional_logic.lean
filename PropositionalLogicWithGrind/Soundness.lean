import PropositionalLogic.Syntax
import PropositionalLogic.Semantics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lemmas

open Fml
open Classical

universe u

variable {α : Type u}

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
