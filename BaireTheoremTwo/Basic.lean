import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option linter.style.longLine false
noncomputable section

open scoped Topology
open Filter Set TopologicalSpace

variable {X Y α : Type*} {ι : Sort*}

section BaireTheoremTwo

variable [TopologicalSpace X] [BaireSpace X]
variable [MetricSpace Y] [CompleteSpace Y]
--variable [MetricSpace Z]

/--
Potentially could simplified with Dense.exists_mem_open which is:
  (hs : Dense s) {U : Set X} (ho : IsOpen U) (hne : U.Nonempty) : ∃ x ∈ s, x ∈ U
-/

theorem dense_set_intersect_open_nonempty {U : Set X} {V : Set X}
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

theorem dense_set_intersect_open_nonempty_v2 {U : Set X} {V : Set X}
     (hU : IsOpen U) (hne : U.Nonempty) (hd : Dense V) :
    (U ∩ V).Nonempty := by
    sorry
  -- rw [Set.nonempty_def]
  -- rw [Set.mem_inter_iff x U V]
  -- rw [Dense.exists_mem_open hd hU hne] at hne


theorem set_dense_iff_intersect_open_nonempty {s : Set Y} :
    Dense s ↔ ∀ (U : Set Y), IsOpen U → U.Nonempty → (U ∩ s).Nonempty := by
  exact dense_iff_inter_open

lemma exist_open_ball_smaller_radius_subset {P : Set Y} {r : ℝ} (hr : 0 < r) (U : Set Y)
    (hUopen : IsOpen U) (hUne : U.Nonempty) (hPOpen : IsOpen P) (hPDense : Dense P) :
    ∃ (x : Y) (r2 : ℝ), r2 > 0 ∧ (Metric.closedBall x r2 ⊆ U ∩ P) ∧ r2 < r := by
    have h_inter_nonempty : (U ∩ P).Nonempty := by
      exact set_dense_iff_intersect_open_nonempty.mp hPDense U hUopen hUne
    have open_inter : IsOpen (U ∩ P) := by
      apply IsOpen.inter hUopen hPOpen
    rw [nonempty_def] at h_inter_nonempty
    have exists_any_ball : ∃ (f : Y) (g: ℝ), f ∈ U ∩ P ∧ g > 0 ∧ Metric.ball f g ⊆ U ∩ P := by
      rcases h_inter_nonempty with ⟨x0, hx0⟩
      use x0
      rcases Metric.isOpen_iff.mp open_inter x0 hx0 with ⟨ε, hε_pos, h_ball_subset⟩
      use ε
    rcases exists_any_ball with ⟨x0, g1, hx0, hg1, hg2⟩
    use x0
    use min (g1/2) (r / 2)
    constructor
    · apply lt_min (half_pos hg1) (half_pos hr)
    · constructor
      · apply Subset.trans (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left (g1/2) (r/2)) (half_lt_self (hg1)))) hg2
      · exact min_lt_of_right_lt (half_lt_self hr)


lemma exists_nested_balls_sequence {W: Set Y} {U: ℕ → Set Y}
(hWopen : IsOpen W) (hWne: W.Nonempty) (hUnopen: ∀ n, IsOpen (U n)) (hUdense: ∀ n, Dense (U n)):
∃ (r_seq: ℕ → ℝ) (x_seq: ℕ → Y), ((∀ n, Metric.closedBall (x_seq (n+1)) (r_seq (n+1)) ⊆ Metric.ball (x_seq n) (r_seq n)
∧ Metric.closedBall (x_seq 0) (r_seq 0) ⊆ W ∩ U 0) ∧ (∀ n, r_seq n ≤ 1/2^n)) := by

  sorry

theorem complete_metric_has_baire_property {f : ℕ → Set Y} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) :=

    by
    rw [dense_iff_inter_open]
    intro U hUopen hUnempty
    --- construct a Cauchy sequence by taking nested balls
    --- then use completeness to get a limit point in the intersection
    sorry

theorem open_mapping_theorem {f : X → Y} (hf : Continuous f) (hopen : ∀ U : Set X, IsOpen U → IsOpen (f '' U))
    (h_surj : Surjective f) : OpenMap f := by

  sorry

theorem dense_iInter_of_isOpen_nat {f : ℕ → Set X} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) :=
  BaireSpace.baire_property f ho hd


end BaireTheoremTwo
