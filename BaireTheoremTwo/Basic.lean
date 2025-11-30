import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic

import Mathlib.Topology.Sequences
import Mathlib.Topology.Closure
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.UniformSpace.Cauchy


set_option linter.style.longLine false
noncomputable section

open scoped Topology
open Filter Set TopologicalSpace

variable {X Y α B B1 : Type*} {ι : Sort*}

section BaireTheoremTwo

variable [TopologicalSpace X] [BaireSpace X]
variable [MetricSpace Y] [CompleteSpace Y] [IsCompletelyMetrizableSpace Y]
--variable [MetricSpace Z]

/--
Potentially could simplified with Dense.exists_mem_open which is:
  (hs : Dense s) {U : Set X} (ho : IsOpen U) (hne : U.Nonempty) : ∃ x ∈ s, x ∈ U
-/
theorem dense_set_intersect_open_nonempty {U : Set X} {V : Set X}
     (hU : IsOpen U) (hne : U.Nonempty) (hd : Dense V) :
    (U ∩ V).Nonempty := by
  by_contra h_empty

  have UsubVc : U ⊆ Vᶜ := by
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
    have exists_any_ball : ∃ (f : Y) (g: ℝ), f ∈ U ∩ P ∧ g > 0
    ∧ Metric.ball f g ⊆ U ∩ P := by
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
      · apply Subset.trans (Metric.closedBall_subset_ball
      (lt_of_le_of_lt (min_le_left (g1/2) (r/2)) (half_lt_self (hg1)))) hg2
      · exact min_lt_of_right_lt (half_lt_self hr)


lemma exists_nested_balls_sequence {W: Set Y} {U: ℕ → Set Y}
(hWopen : IsOpen W) (hWne : W.Nonempty) (hUnopen : ∀ n, IsOpen (U n)) (hUdense : ∀ n, Dense (U n)) :
∃ (r_seq: ℕ → ℝ) (x_seq: ℕ → Y), (((∀ n, Metric.closedBall (x_seq (n+1)) (r_seq (n+1)) ⊆ (Metric.ball (x_seq n) (r_seq n) ∩ U n))
∧ (Metric.closedBall (x_seq 0) (r_seq 0) ⊆ W ∩ U 0)) ∧ (∀ n, 0 < r_seq n ∧  r_seq n ≤ 1/2^n)) := by

  sorry

/--
The primary form of the Baire Category Theorem:
  The countable intersection of dense open sets in a complete metric space is dense.
-/
theorem complete_metric_has_baire_property {f : ℕ → Set Y} (ho : ∀ n, IsOpen (f n))
  (hd : ∀ n, Dense (f n))
  : Dense (⋂ n, f n) := by

  rw [dense_iff_inter_open]
  intro U hUopen hUnempty
  have exists_nested_balls := exists_nested_balls_sequence hUopen hUnempty ho hd
  rcases exists_nested_balls with ⟨r_seq, x_seq, h_nested_balls⟩

  have hSeqIsCauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x_seq n) (x_seq N) < ε := by
    intro ε hε
    rcases h_nested_balls with ⟨h_nested, h_rseq_bound⟩

    -- find N such that r_seq N < ε/2
    have exists_N : ∃ N, r_seq N < ε / 2 := by
      -- since r_seq n ≤ 1/2^n, we can choose N large enough
      -- use Nat.find (fun n => r_seq n < ε / 2)
      sorry

    rcases exists_N with ⟨N, h_rseq_N⟩
    refine ⟨N, ?_⟩
    intro n hn_ge_N

    have hn_seq_in_N_ball :
        Metric.closedBall (x_seq n) (r_seq n) ⊆ Metric.closedBall (x_seq N) (r_seq N) := by
      -- use the nested balls property to show x_seq n is in the closed ball around x_seq N
      induction n, hn_ge_N using Nat.le_induction with
      | base =>
        simp
      | succ k kgtN hk =>
        have ball_k_subset_closedBall_k : Metric.ball (x_seq k) (r_seq k) ∩ f k ⊆ Metric.closedBall (x_seq k) (r_seq k) := by
          exact Set.Subset.trans (Set.inter_subset_left) Metric.ball_subset_closedBall
        exact Set.Subset.trans (
          Set.Subset.trans (h_nested.left k) ball_k_subset_closedBall_k
          ) hk

    have x_seq_n_in_N_ball : x_seq n ∈ Metric.closedBall (x_seq N) (r_seq N) := by
      sorry
      -- exact Set.mem_of_mem_of_subset (Metric.mem_closedBall_self (x_seq n)) hn_seq_in_N_ball
    have x_n_dist_x_N_is_r_N :=
      Metric.mem_closedBall.mp x_seq_n_in_N_ball

    calc
      dist (x_seq n) (x_seq N) ≤ r_seq N := x_n_dist_x_N_is_r_N
      _ < ε / 2 := h_rseq_N
      _ < ε := by linarith

  -- now we have shown the sequence is Cauchy
    -- use the nested balls property to show dist (x_seq n) (x_seq N) < ε

  have hSeqLimit : ∃ x_lim : Y, Tendsto (fun n => x_seq n) atTop (𝓝 x_lim) := by
    -- 1. Convert the metric epsilon-N property to the formal CauchySeq property
    have h_cauchy : CauchySeq x_seq := Metric.cauchySeq_iff'.mpr hSeqIsCauchy
    -- 2. Use the fact that Y is a CompleteSpace to show it converges
    exact cauchySeq_tendsto_of_complete h_cauchy

  rcases hSeqLimit with ⟨x_lim, h_tendsto⟩
  have x_lim_in_balls : ∀ (n : ℕ), x_lim ∈ Metric.closedBall (x_seq n) (r_seq n) := by
    intro n
    have x_k_in_ball_x_n : ∀ k ≥ n, x_seq k ∈ Metric.closedBall (x_seq n) (r_seq n) := by
      intro k hk_ge_n
      induction k, hk_ge_n using Nat.le_induction with
      | base =>
        exact Metric.mem_closedBall_self (le_of_lt ((h_nested_balls.right n).left))
      | succ m mgt_n hm_ind =>
        have r_seq_m_gt_zero := (h_nested_balls.right m).left
        -- this is kinda easy but tedious
        sorry

    -- have h_closed := Metric.isClosed_ball (x := x_seq n) (ε := r_seq n)
    have ball_seq_closed : IsSeqClosed (Metric.closedBall (x_seq n) (r_seq n)) := by
      exact IsClosed.isSeqClosed (Metric.isClosed_closedBall (x := x_seq n) ( ε := r_seq n))

    exact IsClosed.mem_of_tendsto
      (Metric.isClosed_closedBall (x := x_seq n) (ε := r_seq n))
      h_tendsto
      (Filter.eventually_atTop.mpr ⟨n, x_k_in_ball_x_n⟩)

  have x_lim_in_f_n : ∀ n, x_lim ∈ f n := by
    intro n
    have h_ball_np1_sub_f_n : ∀ (n : ℕ ), Metric.closedBall (x_seq (n+1)) (r_seq (n+1)) ⊆ f n := by
      intro n
      exact (Set.subset_inter_iff.mp ((h_nested_balls.left).left n)).right
    exact Set.mem_of_mem_of_subset (x_lim_in_balls (n+1)) (h_ball_np1_sub_f_n n)

  have x_lim_in_U : x_lim ∈ U := by
    have h_lim_in_ball_0 : x_lim ∈ Metric.closedBall (x_seq 0) (r_seq 0) := by
      exact x_lim_in_balls 0
    have ball_0_subset_U : Metric.closedBall (x_seq 0) (r_seq 0) ⊆ U  := by
      have ball_0_subset_U_cap_f_0 : Metric.closedBall (x_seq 0) (r_seq 0) ⊆ U ∩ f 0 := by
        exact (h_nested_balls.left).right
      simp at ball_0_subset_U_cap_f_0
      exact ball_0_subset_U_cap_f_0.left
    exact Set.mem_of_mem_of_subset h_lim_in_ball_0 ball_0_subset_U

  have x_lim_in_inter : x_lim ∈ U ∩ ⋂ n, f n := by
    simp_all
  rw [Set.nonempty_def]
  use x_lim

/--
The second form of the Baire Category Theorem:
  In a complete metric space, the union of countably many
  nowhere dense sets cannot be the whole space.
-/
theorem sum_sets_atleast_one_not_nowhere_dense {f : ℕ → Set Y} [Nonempty Y]
   (hUnion : ⋃ n, f n = univ) :
    ∃ n, ¬ IsNowhereDense (f n) := by
  by_contra h_contra
  push_neg at h_contra
  have compl_closure_open : ∀ n, IsOpen (closure (f n))ᶜ := by
    simp
  have compl_closure_dense : ∀ n, Dense (closure (f n))ᶜ := by
    intro n
    rw [dense_iff_inter_open]
    intro U hUopen hUnempty
    by_contra hcontraEmpty
    push_neg at hcontraEmpty
    have hcontraFull : (U ∩ (closure (f n))ᶜ)ᶜ = (∅)ᶜ := by
      simp
      exact hcontraEmpty
    rw [Set.compl_inter] at hcontraFull
    rw [Set.compl_empty] at hcontraFull
    rw [compl_compl] at hcontraFull

    have hUcClosed : IsClosed Uᶜ := by
      have hUccOpen : IsOpen Uᶜᶜ := by
        rw [compl_compl]
        exact hUopen
      exact isOpen_compl_iff.mp hUccOpen

    have hlessThanSpace : interior (closure (f n) ∪ Uᶜ) ⊆  Uᶜ := by
      have hlessThanUc : interior (closure (f n) ∪ Uᶜ) ⊆ interior (closure (f n)) ∪ Uᶜ:= by
        exact  IsClosed.interior_union_right hUcClosed
      rw [h_contra n] at hlessThanUc
      rw [Set.empty_union] at hlessThanUc
      exact hlessThanUc

    have hUc_ne_univ : Uᶜ ≠ univ := by
      rw [Set.compl_ne_univ]
      exact hUnempty
    have hUc_sub_univ : Uᶜ ⊂ univ := by
      exact Set.ssubset_univ_iff.mpr hUc_ne_univ
    rw [Set.union_comm] at hcontraFull

    have intNotUniv : interior (closure (f n) ∪ Uᶜ) ⊂ univ := by
      exact ssubset_of_subset_of_ssubset hlessThanSpace hUc_sub_univ
    have intNotUnivNeq : interior (closure (f n) ∪ Uᶜ) ≠ univ := by
      exact Set.ssubset_univ_iff.mp intNotUniv
    have intEqUniv : interior (closure (f n) ∪ Uᶜ) = interior (univ) := by
      simpa

    rw [interior_univ] at intEqUniv
    contradiction

  have compl_closure_inter_dense : Dense (⋂ n, (closure (f n))ᶜ) := by
    exact complete_metric_has_baire_property compl_closure_open compl_closure_dense
  have compl_closure_inter_eq : (⋂ n, (closure (f n))ᶜ) = (⋃ n, closure (f n))ᶜ := by
    simp
  rw [compl_closure_inter_eq] at compl_closure_inter_dense
  have int_eq_empty : interior (⋃ n, (closure (f n))) = ∅ := by
    exact interior_eq_empty_iff_dense_compl.mpr compl_closure_inter_dense

  have union_closure_eq_space : (⋃ n, closure (f n)) = univ := by
    have union_closure_sub_univ : (⋃ n, closure (f n)) ⊆ univ := by
      simp
    have univ_sub_union_closure : univ ⊆ (⋃ n, closure (f n)) := by
      have univ_sub_union : univ ⊆ (⋃ n, f n) := by
        exact Set.univ_subset_iff.mpr hUnion
      have union_sub_union_closure : (⋃ n, f n) ⊆ (⋃ n, closure (f n)) := by
        simp
        have f_in_closure : ∀ n, f n ⊆ closure (f n) := by
          simp [subset_closure]

        intro n
        have closure_sub : closure (f n) ⊆ (⋃ n, closure (f n)) := by
          have set_same_subset : closure (f n) ⊆ (closure (f n)) := by
            simp
          exact Set.subset_iUnion_of_subset n set_same_subset
        exact subset_trans (f_in_closure n) closure_sub
      exact subset_trans univ_sub_union union_sub_union_closure

    -- The ⟨a,b⟩ means (a and b)
    exact Set.Subset.antisymm_iff.mpr ⟨union_closure_sub_univ, univ_sub_union_closure⟩

  rw [union_closure_eq_space] at int_eq_empty
  rw [interior_univ] at int_eq_empty
  simp_all


theorem dense_iInter_of_isOpen_nat_v2 {f : ℕ → Set X} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) :=
  BaireSpace.baire_property f ho hd


end BaireTheoremTwo
