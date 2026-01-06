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

variable {α X Z B B1 : Type*} {ι : Sort*}

section BaireTheoremTwo

variable [TopologicalSpace α] [BaireSpace α]
variable [MetricSpace X] [CompleteSpace X] [IsCompletelyMetrizableSpace X]
--variable [MetricSpace Z]

/--
Potentially could simplified with Dense.exists_mem_open which is:
  (hs : Dense s) {U : Set X} (ho : IsOpen U) (hne : U.Nonempty) : ∃ x ∈ s, x ∈ U
-/
theorem dense_set_intersect_open_nonempty {U : Set α} {G : Set α}
     (hU : IsOpen U) (hne : U.Nonempty) (hd : Dense G) :
    (U ∩ G).Nonempty := by
  by_contra h_empty

  have UsubGc : U ⊆ Gᶜ := by
    rw [Set.subset_def]
    intro x hxU hxG
    have xin_inter : x ∈ U ∩ G := Set.mem_inter hxU hxG
    have h_nonempty : (U ∩ G).Nonempty := ⟨x, xin_inter⟩
    contradiction

  have Uc_closed : IsClosed Uᶜ := by
    rw [<-compl_compl U] at hU
    exact isOpen_compl_iff.mp hU

  have GsubUc: G ⊆ Uᶜ := by
    exact Set.subset_compl_comm.mp UsubGc

  have Gclosure_subUc: closure G ⊆ Uᶜ := by
    exact (IsClosed.closure_subset_iff Uc_closed).mpr GsubUc
  have Uc_neq_univ : Uᶜ ≠ univ := by
    exact Set.compl_ne_univ.mpr hne

  have Uc_sub_univ : Uᶜ ⊂ univ := by
    exact Set.ssubset_univ_iff.mpr Uc_neq_univ

  have Gclosure_sub_univ : closure G ⊂ univ := by
    exact Set.ssubset_of_subset_of_ssubset Gclosure_subUc Uc_sub_univ

  have Gclosure_neq_univ : closure G ≠  univ := by
    exact Set.ssubset_univ_iff.mp Gclosure_sub_univ

  have Gclosure_eq_univ : closure G = univ := by
    exact Dense.closure_eq hd

  contradiction

-- theorem dense_set_intersect_open_nonempty_v2 {U : Set α} {G : Set α}
   --  (hU : IsOpen U) (hne : U.Nonempty) (hd : Dense G) :
    -- (U ∩ G).Nonempty := by
    -- sorry
  -- rw [Set.nonempty_def]
  -- rw [Set.mem_inter_iff x U G]
  -- rw [Dense.exists_mem_open hd hU hne] at hne


theorem set_dense_iff_intersect_open_nonempty {s : Set X} :
    Dense s ↔ ∀ (U : Set X), IsOpen U → U.Nonempty → (U ∩ s).Nonempty := by
  exact dense_iff_inter_open

lemma exist_open_ball_smaller_radius_subset {G : Set X} {r : ℝ} (hr : 0 < r) (U : Set X)
    (hUopen : IsOpen U) (hUne : U.Nonempty) (hGOpen : IsOpen G) (hGDense : Dense G) :
    ∃ (x : X) (r2 : ℝ), r2 > 0 ∧ (Metric.closedBall x r2 ⊆ U ∩ G) ∧ r2 < r := by
    have h_inter_nonempty : (U ∩ G).Nonempty := by
      exact set_dense_iff_intersect_open_nonempty.mp hGDense U hUopen hUne
    have open_inter : IsOpen (U ∩ G) := by
      apply IsOpen.inter hUopen hGOpen
    rw [nonempty_def] at h_inter_nonempty
    have exists_any_ball : ∃ (f : X) (g: ℝ), f ∈ U ∩ G ∧ g > 0
    ∧ Metric.ball f g ⊆ U ∩ G := by
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


lemma exists_nested_balls_sequence {U : Set X} {G : ℕ → Set X}
(hUopen : IsOpen U) (hUne : U.Nonempty) (hGopen : ∀ n, IsOpen (G n)) (hGdense : ∀ n, Dense (G n)) :
∃ (r: ℕ → ℝ) (x: ℕ → X), (∀ n, Metric.closedBall (x (n+1)) (r (n+1)) ⊆ (Metric.ball (x n) (r n) ∩ G n))
∧ (Metric.closedBall (x 0) (r 0) ⊆ U ∩ G 0) ∧ (∀ n, 0 < r n ∧  r n ≤ 1/2^n) := by


  -- 1. krok bazowyy (n=0)
  -- szukamy kuli w U ∩ G 0 o promieniu mniejszym niz 1
  have exists_zero : ∃ (x : X) (r : ℝ), r > 0 ∧ Metric.closedBall x r ⊆ U ∩ G 0 ∧ r < 1 := by
    apply exist_open_ball_smaller_radius_subset zero_lt_one U hUopen hUne (hGopen 0) (hGdense 0)
  -- rozpakowuje pieknie istnienie kuli poczatkowej
  rcases exists_zero with ⟨x0, r0, hr0_pos, h0_sub, hr0_lt⟩

  -- 2. krok rekurencyjny
  -- dla każdej kuli (xn, rn) istnieje mniejsza kula wewnątrz niej przeciętej z G n

  have exists_next : ∀ (n : ℕ) (xn : X) (rn : ℝ),
      rn > 0 → ∃ xn_next rn_next, rn_next > 0 ∧
      Metric.closedBall xn_next rn_next ⊆ Metric.ball xn rn ∩ G n ∧
      rn_next < 1 / 2 ^ (n + 1) := by

    intro n xn rn hrn_pos
    let Un := Metric.ball xn rn
    have hUn_open : IsOpen Un := Metric.isOpen_ball
    have hUn_ne : Un.Nonempty := Metric.nonempty_ball.mpr hrn_pos
    -- Promień musi być mniejszy niż 1/2^(n+1)
    have h_rad_limit_pos : 0 < (1 / 2 : ℝ) ^ (n + 1) := by
      simp;

    -- Używamy lematu pomocniczego dla kuli Un i zbioru gęstego G n
    rcases exist_open_ball_smaller_radius_subset h_rad_limit_pos Un hUn_open hUn_ne (hGopen n) (hGdense n)
      with ⟨xn_next, rn_next, hrn_next_pos, h_sub, h_rad_lt⟩

    use xn_next, rn_next
    constructor
    · exact hrn_next_pos
    · constructor
      · exact h_sub
      · simp
        simp at h_rad_lt
        exact h_rad_lt
  -- 3. Zbieramy wszystko razem używając zasady wyboru (!!dopisac do wstepu)
  choose! x r h_next using exists_next
 -- let rec xr_seq : ℕ → X × ℝ := fun n => if n = 0 then (x0, r0)
 --   else (x n (xr_seq (n - 1)).1 (xr_seq (n - 1)).2, r n (xr_seq (n - 1)).1 (xr_seq (n - 1)).2)
  let xr_seq : ℕ → X × ℝ := fun n =>
    Nat.recOn n (x0, r0) (fun n' prev => (x n' prev.1 prev.2, r n' prev.1 prev.2))
  let x_seq : ℕ → X := fun n => (xr_seq n).1
  let r_seq : ℕ → ℝ := fun n => (xr_seq n).2
  have r_seq_pos : ∀ n, r_seq n > 0 := by
    intro n
    induction n with
     -- przypadek bazowy n=0
      | zero => dsimp [r_seq]
                exact hr0_pos
      | succ k ih => dsimp [r_seq]
                     dsimp [xr_seq]
                     apply (h_next k (x_seq k) (r_seq k) (ih)).1


  use r_seq, x_seq
  constructor
  · intro n
    induction n with
     -- przypadek bazowy n=0
      | zero => rw [zero_add]
                dsimp [x_seq, r_seq]
                dsimp [xr_seq]
                exact (h_next 0 x0 r0 hr0_pos).2.1
      | succ k ih => --rw [Nat.add_succ]
                     dsimp [x_seq, r_seq]
                     dsimp [xr_seq]
                     exact (h_next (k + 1) (x_seq (k+1)) (r_seq (k+1)) (r_seq_pos (k+1))).2.1

  · constructor
    · dsimp [x_seq, r_seq]
      dsimp [xr_seq]
      exact h0_sub

    intro n
    constructor
    · exact r_seq_pos n

    · dsimp [r_seq]

      induction n with
       -- przypadek bazowy n=0
        | zero => dsimp [xr_seq]
                  simp
                  exact (le_of_lt hr0_lt)
        | succ k ih =>
            have h_prev := (h_next k (x_seq k) (r_seq k) (r_seq_pos k)).2.2
            simp at h_prev
            dsimp [xr_seq]
            simp
            exact (le_of_lt h_prev)


/--
The primary form of the Baire Category Theorem:
  The countable intersection of dense open sets in a complete metric space is dense.
-/
theorem complete_metric_has_baire_property {G : ℕ → Set X} (ho : ∀ n, IsOpen (G n))
  (hd : ∀ n, Dense (G n))
  : Dense (⋂ n, G n) := by

  rw [dense_iff_inter_open]
  intro U hUopen hUnempty
  have exists_nested_balls := exists_nested_balls_sequence hUopen hUnempty ho hd
  rcases exists_nested_balls with ⟨r, x, h_nested_balls⟩
  rcases h_nested_balls with ⟨h_nested, h_nested0, h_r_bound⟩

  have hSeqIsCauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x n) (x N) < ε := by
    intro ε hε

    -- find N such that r N < ε/2
    have exists_N : ∃ N, r N < ε / 2 := by
      -- since r n ≤ 1/2^n, we can choose N large enough
      -- apply Nat.find (fun n => r n < ε / 2)
      -- Use the lemma that (1/2)^n can be made arbitrarily small

      rcases exists_pow_lt_of_lt_one (half_pos hε) one_half_lt_one with ⟨N, hN⟩
      use N
      -- If we just skip these simps than what we get is a difference
      -- between (1 / 2) ^ N and 1 / 2 ^ N
      -- and with the simp-s we unify the form so that what we compare is the same
      simp at hN
      simp at h_r_bound
      exact LT.lt.trans_le' hN (h_r_bound N).right

    rcases exists_N with ⟨N, h_r_N⟩
    -- Instead of `refine ⟨N, ?_⟩` we can just do:
    use N
    intro n hn_ge_N

    have hn_seq_in_N_ball :
        Metric.closedBall (x n) (r n) ⊆ Metric.closedBall (x N) (r N) := by
      -- use the nested balls property to show x n is in the closed ball around x N
      induction n, hn_ge_N using Nat.le_induction with
      | base =>
        simp
      | succ k kgtN hk =>
        have ball_k_subset_closedBall_k : Metric.ball (x k) (r k) ∩ G k ⊆ Metric.closedBall (x k) (r k) := by
          exact Set.Subset.trans (Set.inter_subset_left) Metric.ball_subset_closedBall
        exact Set.Subset.trans (
          Set.Subset.trans (h_nested k) ball_k_subset_closedBall_k
          ) hk

    have x_seq_n_in_N_ball : x n ∈ Metric.closedBall (x N) (r N) := by
      apply hn_seq_in_N_ball
      apply Metric.mem_closedBall_self
      exact le_of_lt (h_r_bound n).left

      -- exact Set.mem_of_mem_of_subset (Metric.mem_closedBall_self (x n)) hn_seq_in_N_ball
    have x_n_dist_x_N_is_r_N :=
      Metric.mem_closedBall.mp x_seq_n_in_N_ball

    calc
      dist (x n) (x N) ≤ r N := x_n_dist_x_N_is_r_N
      _ < ε / 2 := h_r_N
      _ < ε := by linarith

  -- now we have shown the sequence is Cauchy
    -- use the nested balls property to show dist (x n) (x N) < ε

  have hSeqLimit : ∃ x_lim : X, Tendsto (fun n => x n) atTop (𝓝 x_lim) := by
    -- 1. Convert the metric epsilon-N property to the formal CauchySeq property
    have h_cauchy : CauchySeq x := Metric.cauchySeq_iff'.mpr hSeqIsCauchy
    -- 2. Use the fact that X is a CompleteSpace to show it converges
    exact cauchySeq_tendsto_of_complete h_cauchy

  rcases hSeqLimit with ⟨x_lim, h_tendsto⟩

  have x_lim_in_balls : ∀ (n : ℕ), x_lim ∈ Metric.closedBall (x n) (r n) := by
    intro n

    have ball_m_subset_ball_n : ∀ m ≥ n, Metric.closedBall (x m) (r m) ⊆ Metric.closedBall (x n) (r n) := by
      intro m mgt_n
      induction m, mgt_n using Nat.le_induction with
      | base =>
        exact subset_rfl
      | succ i hi_ge_n hi_subset =>
        -- Wiemy z h_nested_balls, że B_{i+1} ⊆ B_i
        have step_nested := (h_nested i)
        -- B_{i+1} ⊆ ball(i) ⊆ closedBall(i)
        have step_sub : Metric.closedBall (x (i + 1)) (r (i + 1)) ⊆ Metric.closedBall (x i) (r i) := by
          exact Subset.trans step_nested (Subset.trans Set.inter_subset_left Metric.ball_subset_closedBall)
        -- Z przechodniości: B_{i+1} ⊆ B_i ⊆ B_n
        exact Subset.trans step_sub hi_subset

    have x_k_in_ball_x_n : ∀ k ≥ n, x k ∈ Metric.closedBall (x n) (r n) := by
      intro k hk_ge_n
      induction k, hk_ge_n using Nat.le_induction with
      | base =>
        exact Metric.mem_closedBall_self (le_of_lt ((h_r_bound n).left))
      | succ m mgt_n hm_ind =>
        -- 1. Teraz pokazujemy, że x_{m+1} leży w kuli m-tej
        have x_next_in_ball_m : x (m + 1) ∈ Metric.closedBall (x m) (r m) := by
          -- Bierzemy własność zagnieżdżenia dla m: B_{m+1} ⊆ B_m
          have step := (h_nested m)
          -- x_{m+1} jest środkiem B_{m+1}, więc w niej leży
          have center_in_self : x (m + 1) ∈ Metric.closedBall (x (m + 1)) (r (m + 1)) :=
            Metric.mem_closedBall_self (le_of_lt (h_r_bound (m + 1)).left)

          -- Skoro jest w B_{m+1}, a B_{m+1} ⊆ B_m, to jest w B_m
          apply (Subset.trans step (Subset.trans Set.inter_subset_left Metric.ball_subset_closedBall))
          exact center_in_self

        -- 2. Konkluzja: Skoro x_{m+1} ∈ B_m, a B_m ⊆ B_n, to x_{m+1} ∈ B_n
        exact (ball_m_subset_ball_n m mgt_n) x_next_in_ball_m

    -- have h_closed := Metric.isClosed_ball (x := x n) (ε := r n)
    have ball_seq_closed : IsSeqClosed (Metric.closedBall (x n) (r n)) :=
      IsClosed.isSeqClosed (Metric.isClosed_closedBall (x := x n) ( ε := r n))

    exact IsClosed.mem_of_tendsto
      (Metric.isClosed_closedBall (x := x n) (ε := r n))
      h_tendsto
      (Filter.eventually_atTop.mpr ⟨n, x_k_in_ball_x_n⟩)

  have x_lim_in_G_n : ∀ n, x_lim ∈ G n := by
    intro n
    have h_ball_np1_sub_G_n : ∀ (n : ℕ ), Metric.closedBall (x (n+1)) (r (n+1)) ⊆ G n := by
      intro n
      exact (Set.subset_inter_iff.mp (h_nested n)).right
    exact Set.mem_of_mem_of_subset (x_lim_in_balls (n+1)) (h_ball_np1_sub_G_n n)

  have x_lim_in_U : x_lim ∈ U := by
    have h_lim_in_ball_0 : x_lim ∈ Metric.closedBall (x 0) (r 0) := by
      exact x_lim_in_balls 0
    have ball_0_subset_U : Metric.closedBall (x 0) (r 0) ⊆ U  := by
      have ball_0_subset_U_cap_G_0 : Metric.closedBall (x 0) (r 0) ⊆ U ∩ G 0 := by
        exact h_nested0
      simp at ball_0_subset_U_cap_G_0
      exact ball_0_subset_U_cap_G_0.left
    exact Set.mem_of_mem_of_subset h_lim_in_ball_0 ball_0_subset_U

  have x_lim_in_inter : x_lim ∈ U ∩ ⋂ n, G n := by
    simp_all
  rw [Set.nonempty_def]
  use x_lim

/--
The second form of the Baire Category Theorem:
  In a complete metric space, the union of countably many
  nowhere dense sets cannot be the whole space.
-/
theorem sum_sets_atleast_one_not_nowhere_dense {G : ℕ → Set X} [Nonempty X]
   (hUnion : ⋃ n, G n = univ) :
    ∃ n, ¬ IsNowhereDense (G n) := by
  by_contra h_contra
  push_neg at h_contra
  have compl_closure_open : ∀ n, IsOpen (closure (G n))ᶜ := by
    simp
  have compl_closure_dense : ∀ n, Dense (closure (G n))ᶜ := by
    intro n
    rw [dense_iff_inter_open]
    intro U hUopen hUnempty
    by_contra hcontraEmpty
    push_neg at hcontraEmpty
    have hcontraFull : (U ∩ (closure (G n))ᶜ)ᶜ = (∅)ᶜ := by
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

    have hlessThanSpace : interior (closure (G n) ∪ Uᶜ) ⊆  Uᶜ := by
      have hlessThanUc : interior (closure (G n) ∪ Uᶜ) ⊆ interior (closure (G n)) ∪ Uᶜ:= by
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

    have intNotUniv : interior (closure (G n) ∪ Uᶜ) ⊂ univ := by
      exact ssubset_of_subset_of_ssubset hlessThanSpace hUc_sub_univ
    have intNotUnivNeq : interior (closure (G n) ∪ Uᶜ) ≠ univ := by
      exact Set.ssubset_univ_iff.mp intNotUniv
    have intEqUniv : interior (closure (G n) ∪ Uᶜ) = interior (univ) := by
      simpa

    rw [interior_univ] at intEqUniv
    contradiction

  have compl_closure_inter_dense : Dense (⋂ n, (closure (G n))ᶜ) := by
    exact complete_metric_has_baire_property compl_closure_open compl_closure_dense
  have compl_closure_inter_eq : (⋂ n, (closure (G n))ᶜ) = (⋃ n, closure (G n))ᶜ := by
    simp
  rw [compl_closure_inter_eq] at compl_closure_inter_dense
  have int_eq_empty : interior (⋃ n, (closure (G n))) = ∅ := by
    exact interior_eq_empty_iff_dense_compl.mpr compl_closure_inter_dense

  have union_closure_eq_space : (⋃ n, closure (G n)) = univ := by
    have union_closure_sub_univ : (⋃ n, closure (G n)) ⊆ univ := by
      simp
    have univ_sub_union_closure : univ ⊆ (⋃ n, closure (G n)) := by
      have univ_sub_union : univ ⊆ (⋃ n, G n) := by
        exact Set.univ_subset_iff.mpr hUnion
      have union_sub_union_closure : (⋃ n, G n) ⊆ (⋃ n, closure (G n)) := by
        simp
        have G_in_closure : ∀ n, G n ⊆ closure (G n) := by
          simp [subset_closure]

        intro n
        have closure_sub : closure (G n) ⊆ (⋃ n, closure (G n)) := by
          have set_same_subset : closure (G n) ⊆ (closure (G n)) := by
            simp
          exact Set.subset_iUnion_of_subset n set_same_subset
        exact subset_trans (G_in_closure n) closure_sub
      exact subset_trans univ_sub_union union_sub_union_closure

    -- The ⟨a,b⟩ means (a and b)
    exact Set.Subset.antisymm_iff.mpr ⟨union_closure_sub_univ, univ_sub_union_closure⟩

  rw [union_closure_eq_space] at int_eq_empty
  rw [interior_univ] at int_eq_empty
  simp_all


theorem dense_iInter_of_isOpen_nat2 {G : ℕ → Set α} (ho : ∀ n, IsOpen (G n))
    (hd : ∀ n, Dense (G n)) : Dense (⋂ n, G n) :=
  BaireSpace.baire_property G ho hd



end BaireTheoremTwo
