import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Topology.Closure

noncomputable section

open scoped Topology
open Filter Set TopologicalSpace

variable {X Y α : Type*} {ι : Sort*}

section BaireTheoremTwo

variable [TopologicalSpace X] [BaireSpace X]
variable [TopologicalSpace Y] [MetricSpace Y] [CompleteSpace Y]

theorem dense_set_intersect_open_nonempty (U : Set Y) (V : Set Y)
     (hU : IsOpen U) (hne : U.Nonempty) (hd : Dense V) :
    (U ∩ V).Nonempty := by
  by_contra h_empty

  have UsubVc: U ⊆ Vᶜ := by
    rw [Set.subset_def]
    intro x hxU hxV
    have xin_inter : x ∈ U ∩ V := Set.mem_inter hxU hxV
    have h_nonempty : (U ∩ V).Nonempty := ⟨x, xin_inter⟩
    contradiction

  have Uc_closed : IsClosed Uᶜ := by
    rw [<-compl_compl U] at hU
    exact isOpen_compl_iff.mp hU

  have VsubUc: V ⊆ Uᶜ := by
    exact Set.subset_compl_comm.mp UsubVc

  have Vclosure_subUc: closure V ⊆ Uᶜ := by
    exact (IsClosed.closure_subset_iff Uc_closed).mpr VsubUc
  have Uc_neq_univ : Uᶜ ≠ univ := by
    exact Set.compl_ne_univ.mpr hne

  have Uc_sub_univ : Uᶜ ⊂ univ := by
    exact Set.ssubset_univ_iff.mpr Uc_neq_univ

  have Vclosure_sub_univ : closure V ⊂ univ := by
    exact Set.ssubset_of_subset_of_ssubset Vclosure_subUc Uc_sub_univ

  have Vclosure_neq_univ : closure V ≠  univ := by
    exact Set.ssubset_univ_iff.mp Vclosure_sub_univ

  have Vclosure_eq_univ : closure V = univ := by
    exact Dense.closure_eq hd

  contradiction



theorem dense_cM_iInter_of_isOpen_nat {f : ℕ → Set Y} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) :=
    -- From topology without tears
    by
    intro U hUopen hUne

    sorry

theorem dense_iInter_of_isOpen_nat {f : ℕ → Set X} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) :=
  BaireSpace.baire_property f ho hd


end BaireTheoremTwo
