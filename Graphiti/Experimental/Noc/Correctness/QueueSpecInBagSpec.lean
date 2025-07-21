import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Graphiti.Core.Component
import Graphiti.Projects.Noc.Lang
import Graphiti.Projects.Noc.BuildModule
import Graphiti.Projects.Noc.Spec

namespace Graphiti.Projects.Noc

variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

variable (n : Noc Data netsz)

def φ (I : n.spec_mqueueT) (S : n.spec_bagT) : Prop :=
  ∀ (src : n.topology.RouterID) (dst : n.topology.RouterID),
    let idx := n.spec_mqueue_idx src dst
    I[idx] ⊆ S

theorem refines_initial :
  Module.refines_initial n.spec_mqueue n.spec_bag (φ n) := by
    dsimp [Module.refines_initial, drcomponents]
    intros i Hi
    subst i
    exists []
    split_ands
    · rfl
    · intros src dst idx v Hv; simp at Hv

theorem refines_φ : n.spec_mqueue ⊑_{φ n} n.spec_bag := by
  intros i s Hφ
  constructor
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs n.spec_mqueue), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at *
    obtain ⟨src, Hsrc⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp [drcomponents] at Hrule
    have_hole Hv : typeOf v = _ := by
      unfold typeOf
      rewrite [Noc.spec_mqueue, RelIO.liftFinf_get]
      dsimp [drcomponents]
    exists s.concat (Hv.mp v)
    exists s.concat (Hv.mp v)
    and_intros
    · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      simpa [drcomponents]
    · constructor
    · intros src' dst'
      dsimp
      intros v' Hv'
      subst mid_i
      unfold φ at Hφ
      specialize Hφ src' dst'
      dsimp at Hφ
      by_cases Heq : (↑src' * netsz + ↑dst') = (↑src * netsz + ↑(Hv.mp v).2)
      · simp only [
          Heq, typeOf, eq_mp_eq_cast, Vector.getElem_set_self, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false
        ] at Hv'
        simp only [Heq, typeOf, eq_mp_eq_cast] at Hφ
        cases Hv'
        · rename_i Hin;
          simp only [
            List.concat_eq_append, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false
          ]
          left; exact Hφ Hin
        · rename_i Heq; simpa [Heq]
      · rw [Vector.getElem_set_ne] at Hv'
        simp only [List.concat_eq_append, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false]
        left
        apply Hφ Hv'
        simp [Heq]
        intro Heq2
        apply Heq
        simpa [Heq2]
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs n.spec_mqueue), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at *
    obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp [drcomponents] at Hrule
    have_hole Hv : typeOf v = _ := by
      unfold typeOf
      rewrite [Noc.spec_mqueue, RelIO.liftFinf_get]
      dsimp [drcomponents]
    obtain ⟨src, Hrule⟩ := Hrule
    subst i
    unfold φ at Hφ
    dsimp at Hφ
    specialize Hφ src idx
    rw [Vector.getElem_set_self, List.cons_subset] at Hφ
    obtain ⟨Hv, _⟩ := Hφ
    obtain ⟨i, Hi⟩ := in_list_idx Hv
    apply Exists.intro s
    apply Exists.intro (List.eraseIdx s i)
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
    dsimp [drcomponents]
    and_intros
    · exact existSR.done _
    · exists i; and_intros
      · rfl
      · dsimp at Hi; simpa [Hi]
    · intros src' dst'
      dsimp
      -- TODO: Case analysis, we need to keep Hφ above instead of specializing
      -- it
      sorry
  · intros rule mid_i Hcontains Hrule
    exists s

theorem ϕ_indistinguishable :
  ∀ i s, φ n i s → Module.indistinguishable n.spec_mqueue n.spec_bag i s := by
    intros i s Hφ
    constructor <;> intros ident new_i v Hrule <;> dsimp [drcomponents] at *
    · case_transition Hcontains : (Module.inputs n.spec_mqueue), ident,
        (PortMap.getIO_not_contained_false' Hrule)
      dsimp [drcomponents] at *
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents] at Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [Noc.spec_mqueue, RelIO.liftFinf_get]
        dsimp [drcomponents]
      apply Exists.intro _
      · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        dsimp [drcomponents]
    · case_transition Hcontains : (Module.outputs n.spec_mqueue), ident,
        (PortMap.getIO_not_contained_false' Hrule)
      dsimp [drcomponents] at *
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents] at Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [Noc.spec_mqueue, RelIO.liftFinf_get]
        dsimp [drcomponents]
      obtain ⟨src, Hrule⟩ := Hrule
      subst i
      apply Exists.intro ?_
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      dsimp [drcomponents]
      and_intros
      · have : (Hv.mp v, idx) ∈ s := by
          apply Hφ src idx; simpa
        have := in_list_idx this
        obtain ⟨i, Hi⟩ := this
        exists i
        and_intros
        · sorry -- TODO: Why cannot I do rfl ?
        · simp only [Fin.getElem_fin, typeOf, eq_mp_eq_cast] at Hi
          simpa [Hi]
      · sorry -- TODO: Solving variable

theorem correct : n.spec_mqueue ⊑ n.spec_bag := by
  apply (
    Module.refines_φ_refines
      (ϕ_indistinguishable n)
      (refines_initial n)
      (refines_φ n)
  )
