import Mathlib
import Domination.General

----------------------------------------------------------------------------------------------------

structure Policy (V : Type*) where
  f : V → Real
  m : Real := 1
  hm : 0 < m := by norm_num
  f₀ : ∀ r, 0 ≤ f r := by aesop
  fₘ : ∀ r, f r ≤ m := by aesop

structure Tiling (G : SimpleGraph V) where
  t : Type*
  f : V → t
  n : Nat
  d : Nat
  n₀ : n ≠ 0 := by norm_num
  d₀ : d ≠ 0 := by norm_num
  h₁ : ∀ t, {v | f v = t}.ncard = n := by aesop
  h₂ : ∀ u v, f u = f v → G.edist u v ≤ d := by aesop

variable {V : Type*} {G : SimpleGraph V} {τ : Tiling G} {π : Policy V} {S : Set V}

----------------------------------------------------------------------------------------------------

noncomputable def Policy.set (S : Set V) : Policy V := {
  f := fun v ↦ have := Classical.propDecidable (v ∈ S); if v ∈ S then 1 else 0
}

@[simp] theorem Policy.sum_eq_inter_ncard (s t : Set V) [Fintype s]
  : ∑ x ∈ s, (Policy.set t).f x = (s ∩ t).ncard := by simp [Policy.set, ←Set.ncard_coe_finset]

theorem Policy.sum_nonneg : 0 ≤ ∑ x ∈ s, π.f x := by simp [Finset.sum_nonneg, π.f₀]

theorem Policy.sum_le_m_ncard [Fintype S] : (∑ x ∈ S, π.f x) ≤ π.m * S.ncard := by
  rw [Set.ncard_eq_toFinset_card' _, mul_comm, ←nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul; simp [π.fₘ]

----------------------------------------------------------------------------------------------------

noncomputable instance Tiling.fintype {t : τ.t} : Fintype {v | τ.f v = t} := by
  apply Set.Finite.fintype; apply Set.finite_of_ncard_ne_zero; rw [τ.h₁ t]; exact τ.n₀

def Tiling.id (G : SimpleGraph V) : Tiling G := { t := V, f := fun v ↦ v, n := 1, d := 1 }

def Tiling.closure (τ : Tiling G) (S : Set V) : Set V :=
  ⋃ t ∈ {t | ∃ u ∈ {x | τ.f x = t}, u ∈ S}, {x | τ.f x = t}

@[simp] theorem Tiling.id_closure : (Tiling.id G).closure S = S := by
  ext x; simp [closure, id]; tauto

@[simp] theorem Tiling.closure_idemp : τ.closure (τ.closure S) = τ.closure S := by
  ext x; constructor <;> simp only [closure, Set.mem_setOf_eq, Set.iUnion_exists, Set.mem_iUnion,
    exists_prop, exists_and_right, exists_eq_right', forall_exists_index, and_imp]
  · intro y hy z hz h; exists z; rw [hz, hy]; simp [h]
  · intro y hy h; exists y; apply And.intro hy; exists y

theorem Tiling.subset_closure : S ⊆ τ.closure S := by
  intro x hx; simp only [closure, Set.mem_setOf_eq, Set.iUnion_exists, Set.mem_iUnion, exists_prop,
    exists_and_right, exists_eq_right']; exists x

theorem Tiling.closure_mono (h : S₁ ⊆ S₂) : τ.closure S₁ ⊆ τ.closure S₂ := by
  intro x; simp only [closure, Set.mem_setOf_eq, Set.iUnion_exists, Set.mem_iUnion, exists_prop,
    exists_and_right, exists_eq_right']; intro ⟨y, hy₁, hy₂⟩; exists y; simp [hy₁, h hy₂]

theorem Tiling.closure_nonempty (h : S.Nonempty) : (τ.closure S).Nonempty := by
  exact Set.Nonempty.mono (s := S) τ.subset_closure h

noncomputable instance Tiling.closure_fintype [Fintype S] : Fintype (τ.closure S) := by
  apply Set.Finite.fintype; unfold closure; apply Set.Finite.biUnion _ (fun _ _ ↦ Set.toFinite _)
  simp_rw [Set.mem_setOf_eq, Set.setOf_exists]; apply Set.Finite.iUnion (t := S) (Set.toFinite _)
  <;> (intro _ h; simp [h])

@[simp] theorem Tiling.biUnion_closure_eq {f : V → Set V}
  : ⋃ x ∈ S, τ.closure (f x) = τ.closure (⋃ x ∈ S, f x) := by
  ext x; constructor <;> simp only [closure, Set.mem_setOf_eq, Set.iUnion_exists, Set.mem_iUnion,
    exists_prop, exists_and_right, exists_eq_right', forall_exists_index, and_imp]
  <;> (intro y hy z hz₁ hz₂; exists z; apply And.intro hz₁; exists y)

----------------------------------------------------------------------------------------------------

def ball (G : SimpleGraph V) (r : Nat) (v : V) : Set V := { u | G.edist u v ≤ r }
def shell (G : SimpleGraph V) (r : Nat) (v : V) : Set V := { u | G.edist u v = r }

def cball (τ : Tiling G) (r : Nat) (v : V) := τ.closure (ball G r v)

----------------------------------------------------------------------------------------------------

@[simp] theorem ball₁ : ball G 1 v = insert v (G.neighborSet v) := by
  ext x; rw [ball, Set.mem_insert_iff, G.mem_neighborSet, or_comm, G.adj_comm]
  exact G.edist_le_one_iff_adj_or_eq

theorem ball_eq_union_ball : ball G (r + 1) v = ⋃ u ∈ ball G 1 v, ball G r u := by
  ext x; constructor <;> simp only [ball, Nat.cast_add, Nat.cast_one, Set.mem_setOf_eq,
    Set.mem_iUnion, exists_prop]
  · intro dvx; rw [G.edist_comm] at dvx
    have ⟨vx, vxl⟩ := G.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by tauto) dvx)
    cases vx with | nil => exists v; simp | @cons v w x vw wx =>
    exists w; apply And.intro (by rw [G.edist_comm]; simp [G.edist_le_one_iff_adj_or_eq, vw])
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] at vxl
    rw [←ENat.add_le_add_iff_right (k := 1) (by decide)]; apply le_trans _ dvx
    rw [←vxl, ENat.add_le_add_iff_right (by decide), G.edist_comm]; apply SimpleGraph.Walk.edist_le
  · intro ⟨y, dyv, dxy⟩; apply le_trans (b := G.edist x y + G.edist y v) G.edist_triangle
    exact add_le_add dxy dyv

theorem ball_nonempty : (ball G r v).Nonempty := by
  apply Set.nonempty_of_mem (x := v); simp [ball]

theorem ball_mono (h : r₁ ≤ r₂) : ball G r₁ v ⊆ ball G r₂ v := by
  intro x hx; rw [ball, Set.mem_setOf_eq] at ⊢ hx; apply le_trans hx; simp [h]

noncomputable instance ball_fintype [G.LocallyFinite] : Fintype (ball G r v) := by
  apply Set.Finite.fintype; induction r generalizing v with | zero => simp [ball] | succ r ih =>
  rw [ball_eq_union_ball]; apply Set.Finite.biUnion
    (by rw [ball₁]; exact Set.finite_insert.mpr (Set.toFinite _)) (fun _ _ ↦ ih)

----------------------------------------------------------------------------------------------------

theorem cball_eq_union_cball : cball τ (r + 1) v = ⋃ u ∈ ball G 1 v, cball τ r u := by
  unfold cball; rw [τ.biUnion_closure_eq, ball_eq_union_ball]

theorem cball_nonempty : (cball τ r v).Nonempty := τ.closure_nonempty ball_nonempty

theorem cball_mono (h : r₁ ≤ r₂) : cball τ r₁ v ⊆ cball τ r₂ v := τ.closure_mono (ball_mono h)

theorem cball_lower : ball G r v ⊆ cball τ r v := τ.subset_closure

theorem cball_upper : cball τ r v ⊆ ball G (r + τ.d) v := by
  intro p h; simp only [cball, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop,
    exists_eq_right', Tiling.closure] at h
  obtain ⟨q, h₁, h₂⟩ := h; apply τ.h₂ at h₁
  simp only [ball, Nat.cast_add, Set.mem_setOf_eq] at ⊢ h₂
  rw [G.edist_comm] at h₁; apply le_trans (b := G.edist p q + G.edist q v) G.edist_triangle
  rw [add_comm]; exact add_le_add h₂ h₁

noncomputable instance cball_fintype [G.LocallyFinite] : Fintype (cball τ r v) := τ.closure_fintype

----------------------------------------------------------------------------------------------------

theorem ball_eq_ball_shell : ball G (r + 1) v = ball G r v ∪ shell G (r + 1) v := by
  ext x; simp only [ball, shell, Set.mem_setOf_eq, Set.mem_union]
  cases G.edist x v with | top => simp; tauto | coe => norm_cast; omega

theorem shell_eq_ball_sub : shell G (r + 1) v = ball G (r + 1) v \ ball G r v := by
  ext x; simp only [ball, shell, Set.mem_setOf_eq, Set.mem_diff]
  cases G.edist x v with | top => simp; tauto | coe => norm_cast; omega

theorem ball_shell_disjoint (h : r₁ < r₂) : Disjoint (ball G r₁ v) (shell G r₂ v) := by
  intro s; simp only [Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]; intro a b
  rw [Set.eq_empty_iff_forall_notMem]; intro x hx
  have gx := hx; apply a at hx; apply b at gx; simp only [ball, shell, Set.mem_setOf_eq] at hx gx
  cases hd : G.edist x v with
  | top => rw [hd] at hx; contradiction
  | coe => rw [hd] at hx gx; norm_cast at hx gx; rw [gx, ←not_lt] at hx; contradiction

noncomputable instance shell_fintype [G.LocallyFinite] : Fintype (shell G r v) := by
  apply Set.Finite.fintype; apply Set.Finite.subset (s := ball G r v) (Set.toFinite _)
  rw [ball, shell, Set.setOf_subset_setOf]; intros; simp [*]

----------------------------------------------------------------------------------------------------

macro "ball!" "[" h:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [
  ball_nonempty, ball_mono,
  cball_nonempty, cball_mono, cball_lower, cball_upper,
  ball_shell_disjoint,
  Policy.sum_nonneg, Policy.sum_le_m_ncard,
  Set.toFinite, Set.ncard_le_ncard, Set.ncard_pos, Set.Nonempty.ne_empty,
  Pi.le_def, one_le_div, div_le_one, div_le_div_iff_of_pos_right, div_nonneg,
  $h,*
])
macro "ball!" : tactic => `(tactic| ball! [])

----------------------------------------------------------------------------------------------------

def slow_growth_at (G : SimpleGraph V) (v : V) (e₁ := 1) (e₂ := 0) := Filter.Tendsto
  (fun r ↦ ((ball G (r + e₁) v).ncard : Real) / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 1)

def slow_tiling_at (τ : Tiling G) (v : V) (e₁ := 1) (e₂ := 0) := Filter.Tendsto
  (fun r ↦ ((cball τ (r + e₁) v).ncard : Real) / ((cball τ (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 1)

def slow_boundary_at (G : SimpleGraph V) (v : V) (e₁ e₂ : Nat := 0) := Filter.Tendsto
  (fun r ↦ ((shell G (r + e₁) v).ncard : Real) / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 0)

----------------------------------------------------------------------------------------------------

theorem slow_tiling_at_ext [G.LocallyFinite]
  (e₃ := 1) (e₄ := 0) (h₁₂ : e₁ ≠ e₂ := by omega) (h₃₄ : e₃ ≠ e₄ := by omega)
  : slow_tiling_at τ v e₁ e₂ ↔ slow_tiling_at τ v e₃ e₄ := by
  let rec helper : ∀ e₁ e₂, e₂ < e₁ → (slow_tiling_at τ v e₁ e₂ ↔ slow_tiling_at τ v)
  | 0, _, _ => by contradiction
  | e₁ + 1, e₂ + 1, _ => by
    simp_rw [←helper e₁ e₂ (by omega), slow_tiling_at, add_comm e₁, add_comm e₂, ←add_assoc]
    nth_rw 2 [←Filter.tendsto_add_atTop_iff_nat 1]
  | e₁ + 1, 0, _ => by
    cases Decidable.em (e₁ = 0) with | inl t => simp [t] | inr =>
    rw [←helper e₁ 0 (by omega)]; unfold slow_tiling_at; constructor <;> intro h
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun r ↦ 1) (by simp) h <;> ball!
    · conv =>
        arg 1; ext r; rw [←div_mul_div_cancel₀ (b := ↑(cball τ (r + 1) v).ncard) (by ball!)]
      conv => arg 3; rw [show (1 : Real) = 1 * 1 by simp]
      apply Filter.Tendsto.mul
      · simp_rw [add_comm e₁, ←add_assoc]; rw [←Filter.tendsto_add_atTop_iff_nat 1] at h; exact h
      · rw [←slow_tiling_at] at ⊢ h; rw [helper e₁ 0 (by omega)] at h; exact h
  have assistant : ∀ {e₁ e₂}, e₁ ≠ e₂ → (slow_tiling_at τ v e₁ e₂ ↔ slow_tiling_at τ v) := by
    have t : ∀ e₁ e₂, slow_tiling_at τ v e₁ e₂ → slow_tiling_at τ v e₂ e₁ := fun e₁ e₂ h ↦ by
      unfold slow_tiling_at
      conv => arg 1; ext r; rw [show ∀ a b : Real, a / b = (b / a)⁻¹ by intros; simp]
      conv => arg 3; rw [show (1 : Real) = 1⁻¹ by simp]
      exact Filter.Tendsto.inv₀ h (by simp)
    intro e₁ e₂ _; cases Decidable.em (e₂ < e₁) with | inl h => exact helper e₁ e₂ h | inr =>
    rw [←helper e₂ e₁ (by omega)]; constructor <;> apply t
  rw [assistant h₁₂, assistant h₃₄]

theorem slow_growth_at_ext [G.LocallyFinite]
  (e₃ := 1) (e₄ := 0) (h₁₂ : e₁ ≠ e₂ := by omega) (h₃₄ : e₃ ≠ e₄ := by omega)
  : slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v e₃ e₄ := by
  unfold slow_growth_at
  conv_lhs => arg 1; ext r; repeat rw [←Tiling.id_closure (G := G) (S := ball G _ v), ←cball]
  conv_rhs => arg 1; ext r; repeat rw [←Tiling.id_closure (G := G) (S := ball G _ v), ←cball]
  rw [←slow_tiling_at, ←slow_tiling_at]; exact slow_tiling_at_ext _ _

theorem slow_tiling_at_iff [G.LocallyFinite] (h₁₂ : e₁ ≠ e₂ := by omega)
  : slow_tiling_at τ v e₁ e₂ ↔ slow_growth_at G v e₁ e₂ := by
  constructor <;> intro h
  · unfold slow_growth_at; rw [←Filter.tendsto_add_atTop_iff_nat τ.d]
    simp_rw [add_assoc, add_comm τ.d, ←add_assoc]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun r ↦ ((cball τ (r + e₁) v).ncard : Real) / (cball τ (r + e₂ + τ.d) v).ncard)
      (h := fun r ↦ ((cball τ (r + e₁ + τ.d) v).ncard : Real) / (cball τ (r + e₂) v).ncard)
    · simp_rw [add_assoc]; rw [←slow_tiling_at]
      cases Decidable.em (e₁ = e₂ + τ.d) with | inl t => ball! [t, slow_tiling_at] | inr =>
      rw [slow_tiling_at_ext e₁ e₂]; exact h
    · simp_rw [add_assoc]; rw [←slow_tiling_at]
      cases Decidable.em (e₁ + τ.d = e₂) with | inl t => ball! [t, slow_tiling_at] | inr =>
      rw [slow_tiling_at_ext e₁ e₂]; exact h
    all_goals rw [Pi.le_def]; intro r; apply div_le_div₀ <;> ball!
  · unfold slow_tiling_at; apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun r ↦ ((ball G (r + e₁) v).ncard : Real) / (ball G (r + e₂ + τ.d) v).ncard)
      (h := fun r ↦ ((ball G (r + e₁ + τ.d) v).ncard : Real) / (ball G (r + e₂) v).ncard)
    · simp_rw [add_assoc]; rw [←slow_growth_at]
      cases Decidable.em (e₁ = e₂ + τ.d) with | inl t => ball! [t, slow_growth_at] | inr =>
      rw [slow_growth_at_ext e₁ e₂]; exact h
    · simp_rw [add_assoc]; rw [←slow_growth_at]
      cases Decidable.em (e₁ + τ.d = e₂) with | inl t => ball! [t, slow_growth_at] | inr =>
      rw [slow_growth_at_ext e₁ e₂]; exact h
    all_goals rw [Pi.le_def]; intro r; apply div_le_div₀ <;> ball!

theorem slow_tiling_at_reach [G.LocallyFinite]
  (r : G.Reachable v u := by assumption) (st : slow_tiling_at τ v := by assumption)
  : slow_tiling_at τ u := by
  have helper (v u : V) (r₁ r₂ : Nat) (Avu : G.Adj v u) :
    ((cball τ r₁ v).ncard : Real) / ((cball τ (r₂ + 1) v).ncard : Real) ≤
    ((cball τ (r₁ + 1) u).ncard : Real) / ((cball τ r₂ u).ncard : Real) := by
    apply div_le_div₀ (by simp) _ (by ball!) <;> norm_cast <;> apply Set.ncard_le_ncard _ (by ball!)
    <;> rw [cball_eq_union_cball] <;> exact Set.subset_biUnion_of_mem (by simp [Avu, Avu.symm])
  have ⟨Wvu⟩ := r; induction Wvu with | nil => assumption | @cons v w u Avw Wwu ih =>
  apply ih ⟨Wwu⟩; rw [slow_tiling_at_ext 4 1]; apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((slow_tiling_at_ext 3 2).mp st) ((slow_tiling_at_ext 5).mp st)
    <;> simp [Pi.le_def, helper, Avw, Avw.symm]

theorem slow_growth_at_reach [G.LocallyFinite]
  (r : G.Reachable v u := by assumption) (sg : slow_growth_at G v := by assumption)
  : slow_growth_at G u := by
  rw [←slow_tiling_at_iff (τ := Tiling.id G)] at ⊢ sg; exact slow_tiling_at_reach r

-- note: e₁ < e₂ is not provable in general by counterexample: tree with #children = depth
-- todo: add ext theorem and see if this can be refactored to use it like the others
-- todo: also add reach theorem - could just do it via boundary to sg equivalence
theorem slow_boundary_at_iff [G.LocallyFinite] (h₁₂ : e₂ < e₁ := by omega)
  : slow_boundary_at G v e₁ e₂ ↔ slow_growth_at G v e₁ e₂ := match e₁, e₂ with
  | 0, _ => by contradiction
  | e₁ + 1, e₂ + 1 => by
    have ih := slow_boundary_at_iff (e₁ := e₁) (e₂ := e₂) (v := v)
    simp only [slow_growth_at, slow_boundary_at, add_comm e₁, add_comm e₂, ←add_assoc] at ⊢ ih
    nth_rw 1 [←Filter.tendsto_add_atTop_iff_nat 1] at ih
    nth_rw 2 [←Filter.tendsto_add_atTop_iff_nat 1] at ih; exact ih
  | e₁ + 1, 0 => by
    constructor <;> rw [slow_growth_at, slow_boundary_at] <;> intro h
    · conv =>
        arg 1; ext r
        rw [←add_assoc, ball_eq_ball_shell, Set.ncard_union_eq (by ball!), Nat.cast_add, add_div]
      conv => arg 3; rw [←add_zero 1]
      apply Filter.Tendsto.add _ h; rw [←slow_growth_at]
      cases e₁ with | zero => ball! [slow_growth_at] | succ e₁ =>
      rw [←slow_boundary_at_iff (e₁ := e₁ + 1) (e₂ := 0)]
      have t := tendsto_of_tendsto_of_tendsto_of_le_of_le (α := Real)
        (g := fun r ↦ 0) (by simp) h (by simp [Pi.le_def, div_nonneg])
        (f := fun r ↦ ↑(shell G (r + e₁ + 1 + 1) v).ncard / ↑(ball G (r + 1) v).ncard)
        (by simp_rw [←add_assoc, Pi.le_def]; intro r; apply div_le_div_of_nonneg_left <;> ball!)
      simp_rw [show ∀ r : Nat, r + e₁ + 1 + 1 = r + 1 + e₁ + 1 by intro; ring] at t
      rw [Filter.tendsto_add_atTop_iff_nat 1 (α := Real)
        (f := fun r ↦ ↑(shell G (r + e₁ + 1) v).ncard / ↑(ball G r v).ncard)] at t
      exact t
    · conv =>
        arg 1; ext r
        rw [←add_assoc, shell_eq_ball_sub, Set.ncard_diff (by ball!) (by ball!)]
        rw [Nat.cast_sub (by ball!), sub_div, add_assoc]
      rw [←sub_self 1]; apply Filter.Tendsto.sub h; rw [←slow_growth_at] at ⊢ h
      cases e₁ with | zero => ball! [slow_growth_at] | succ e₁ =>
      rw [slow_growth_at_ext (e₁ + 1 + 1)]; exact h

----------------------------------------------------------------------------------------------------

noncomputable def fudensity_at (G : SimpleGraph V) [G.LocallyFinite]
  (π : Policy V) (v : V) (e₁ e₂ := 0) := Filter.limsup
  (fun r ↦ (∑ x ∈ (ball G (r + e₁) v), π.f x) / ↑(ball G (r + e₂) v).ncard) Filter.atTop

noncomputable def cfudensity_at (τ : Tiling G) [G.LocallyFinite]
  (π : Policy V) (v : V) (e₁ e₂ : Nat := 0) := Filter.limsup
  (fun r ↦ (∑ x ∈ (cball τ (r + e₁) v), π.f x) / ↑(cball τ (r + e₂) v).ncard) Filter.atTop

noncomputable def udensity_at (G : SimpleGraph V) (S : Set V) (v : V) (e₁ e₂ := 0) := Filter.limsup
  (fun r ↦ (((ball G (r + e₁) v) ∩ S).ncard : Real) / ↑(ball G (r + e₂) v).ncard) Filter.atTop

----------------------------------------------------------------------------------------------------

theorem cball_div_eventually_le [G.LocallyFinite] (e₁ e₂ : Nat) (ε : Real := 1)
  (hε : 0 < ε := by omega) (st : slow_tiling_at τ v := by assumption) : ∀ᶠ r in Filter.atTop,
  ((cball τ (r + e₁) v).ncard : Real) / (cball τ (r + e₂) v).ncard ≤ 1 + ε := by
  apply Filter.Tendsto.eventually_le_const (v := 1) (by simp [hε])
  cases Decidable.em (e₁ = e₂) with | inl h => ball! [h] | inr h =>
  rw [←slow_tiling_at, slow_tiling_at_ext]; exact st

theorem cball_fdiv_eventually_le [G.LocallyFinite] (e₁ e₂ : Nat) (ε : Real := 1)
  (hε : 0 < ε := by omega) (st : slow_tiling_at τ v := by assumption) : ∀ᶠ r in Filter.atTop,
  (∑ x ∈ (cball τ (r + e₁) v), π.f x) / (cball τ (r + e₂) v).ncard ≤ π.m + ε := by
  apply Filter.Eventually.mono (cball_div_eventually_le e₁ e₂ (ε / π.m) (div_pos hε π.hm))
  intro r q; apply le_trans (b := π.m * (↑(cball τ (r + e₁) v).ncard / ↑(cball τ (r + e₂) v).ncard))
  · rw [mul_div]; apply div_le_div_of_nonneg_right <;> ball!
  · conv_rhs => rw [←mul_one π.m, ←mul_div_cancel₀ ε (ne_of_lt π.hm).symm, ←mul_add]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt π.hm); exact q

----------------------------------------------------------------------------------------------------

theorem cfudensity_at_ext [G.LocallyFinite]
  (e₃ e₄ : Nat := 0) (st : slow_tiling_at τ v := by assumption)
  : cfudensity_at τ π v e₁ e₂ = cfudensity_at τ π v e₃ e₄ := by
  rw [cfudensity_at, ←Filter.limsup_nat_add _ e₃]; conv_lhs =>
    arg 1; ext r; rw [add_assoc, add_assoc]
    rw [←div_mul_div_cancel₀ (b := ((cball τ (r + (e₁ + e₄)) v).ncard : Real)) (by ball!), mul_comm]
  rw [←one_mul (cfudensity_at τ π v e₃ e₄)]
  apply limsup_mul_eq (m₁ := 2) (m₂ := π.m + 1) _ _ (by ball!) (by ball!) _ _
  · cases Decidable.em (e₁ + e₄ = e₃ + e₂) with | inl h => ball! [h, slow_tiling_at] | inr h =>
    rw [←slow_tiling_at, slow_tiling_at_ext]; exact st
  · simp_rw [add_comm e₃, ←add_assoc]
    rw [Filter.limsup_nat_add (fun r ↦ (∑ x ∈ (cball τ (r + e₃) v).toFinset, π.f x)
      / (cball τ (r + e₄) v).ncard) e₁, ←cfudensity_at]
  · apply Filter.Tendsto.eventually_le_const (v := 1) (by simp)
    cases Decidable.em (e₁ + e₄ = e₃ + e₂) with | inl t => ball! [t] | inr t =>
    rw [←slow_tiling_at, slow_tiling_at_ext]; exact st
  · apply cball_fdiv_eventually_le <;> simp [*]

theorem cfudensity_at_reach [G.LocallyFinite]
  (r : G.Reachable v u := by assumption) (st : slow_tiling_at τ v := by assumption)
  : cfudensity_at τ π v e₁ e₂ = cfudensity_at τ π u e₁ e₂ := by
  obtain ⟨Wvu⟩ := r; induction Wvu with | nil => rfl | @cons v w u Avw Wwu ih =>
  have st' := slow_tiling_at_reach (SimpleGraph.Adj.reachable Avw); rw [←ih st']
  suffices h : ∀ v w, slow_tiling_at τ v → slow_tiling_at τ w → G.Adj w v →
    cfudensity_at τ π v e₁ e₂ ≤ cfudensity_at τ π w e₁ e₂ by
    apply le_antisymm <;> (apply h <;> simp [*, Avw.symm])
  intro v w stv stw Avw; rw [cfudensity_at_ext e₁ (e₂ + 1)]
  apply le_trans (b := cfudensity_at τ π w (e₁ + 1) e₂) _ (by rw [cfudensity_at_ext e₁ e₂])
  unfold cfudensity_at; apply Filter.limsup_le_limsup
  · apply Filter.Eventually.of_forall; intro; apply div_le_div₀ (by ball!) _ (by ball!) _
    · apply Finset.sum_le_sum_of_subset_of_nonneg _ (by ball! [π.f₀])
      rw [Set.subset_toFinset, Set.coe_toFinset, ←add_assoc, cball_eq_union_cball]
      apply Set.subset_biUnion_of_mem; ball! [Avw]
    · norm_cast; apply Set.ncard_le_ncard _ (by ball!); rw [←add_assoc, cball_eq_union_cball]
      apply Set.subset_biUnion_of_mem; ball! [Avw.symm]
  · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; ball!
  · exists π.m + 1; rw [Filter.eventually_map]; apply cball_fdiv_eventually_le <;> simp [*]


-- theorem ufdensity_at_reach [G.LocallyFinite]
--   (r : G.Reachable v u := by assumption) (h : ufdensity_at G π v d := by assumption)
--   (sg : slow_growth_at G v := by assumption)
--   : ufdensity_at G π u d := by
--   have ⟨Wvu⟩ := r; induction Wvu with | nil => assumption | @cons v w u Avw Wwu ih =>
--   apply ih ⟨Wwu⟩ _ (slow_growth_at_reach (SimpleGraph.Adj.reachable Avw))
--   have sgw : slow_growth_at G w := slow_growth_at_reach (SimpleGraph.Adj.reachable Avw)
--   have helper (v u : V) (r₁ r₂ : Nat) (Avu : G.Adj v u) :
--     (∑ x ∈ ball G r₁ v, π.f x) / (ball G (r₂ + 1) v).ncard ≤
--     (∑ x ∈ ball G (r₁ + 1) u, π.f x) / (ball G r₂ u).ncard := by
--     apply div_le_div₀ (by simp) _ (by ball!)
--     · norm_cast; apply Set.ncard_le_ncard _ (by ball!); rw [ball_eq_union_ball]
--       exact Set.subset_biUnion_of_mem (by simp [Avu])
--     · apply Finset.sum_le_sum_of_subset_of_nonneg _ (by simp [π.f₀])
--       rw [Set.subset_toFinset, Set.coe_toFinset, ball_eq_union_ball]
--       exact Set.subset_biUnion_of_mem (by simp [Avu.symm])
--   rw [ufdensity_at_ext 1 1]; apply le_antisymm
--   · apply le_trans (b := Filter.limsup
--       (fun r ↦ (∑ x ∈ ball G (r + 2) v, π.f x) / ↑(ball G (r + 0) v).ncard) Filter.atTop)
--       _ (le_of_eq (by rw [←ufdensity_at, ufdensity_at_ext]; exact h))
--     apply Filter.limsup_le_limsup
--     · apply Filter.Eventually.of_forall; simp [*, Avw.symm]
--     · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; simp
--     · exists π.m + 1; apply fball_div_eventually_le <;> simp [*]
--   · apply le_trans (b := Filter.limsup
--       (fun r ↦ (∑ x ∈ ball G (r + 0) v, π.f x) / ↑(ball G (r + 2) v).ncard) Filter.atTop)
--       (le_of_eq (Eq.symm (by rw [←ufdensity_at, ufdensity_at_ext]; exact h)))
--     apply Filter.limsup_le_limsup
--     · apply Filter.Eventually.of_forall; simp [*]
--     · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; simp
--     · exists π.m + 1; apply fball_div_eventually_le <;> simp [*]











theorem ufdensity_at_ext [G.LocallyFinite]
  {e₁ e₂ : Nat} (e₃ e₄ := 0) (sg : slow_growth_at G v := by assumption)
  : fudensity_at G π v e₁ e₂ = fudensity_at G π v e₃ e₄ := by
  suffices h : ∀ e₁ e₂ e₃ e₄, fudensity_at G π v e₁ e₂ = fudensity_at G π v e₃ e₄ by aesop
  intro e₁ e₂ e₃ e₄
  conv_lhs => rw [fudensity_at, ←Filter.limsup_nat_add _ e₁]; arg 1; ext r; rw [add_assoc]
  conv_rhs => rw [fudensity_at, ←Filter.limsup_nat_add _ e₃]; arg 1; ext r; rw [add_assoc, add_comm e₃]
  conv_lhs =>
    arg 1; ext r
    rw [←div_mul_div_cancel₀ (b := ((ball G (r + (e₂ + e₃)) v).ncard : Real)) (by ball!), mul_comm]
  conv_rhs => rw [←one_mul d]
  apply limsup_mul_eq (m₁ := 2) (m₂ := π.m + 1) _ h (by simp [div_nonneg]) (by simp) _ _
  · cases Decidable.em (e₂ + e₃ = e₁ + e₄) with | inl t => ball! [t] | inr t =>
    rw [←slow_growth_at, slow_growth_at_ext]; exact sg
  · apply Filter.Tendsto.eventually_le_const (v := 1) (by simp)
    cases Decidable.em (e₂ + e₃ = e₁ + e₄) with | inl t => ball! [t] | inr t =>
    rw [←slow_growth_at, slow_growth_at_ext]; exact sg
  · apply fball_div_eventually_le <;> simp [*]




theorem udensity_at_iff_ufdensity_at [G.LocallyFinite]
  : udensity_at G S v d e₁ e₂ ↔ ufdensity_at G (Policy.set S) v d e₁ e₂ := by
  simp [udensity_at, ufdensity_at]

theorem udensity_at_ext [G.LocallyFinite] (e₃ e₄ := 0) (sg : slow_growth_at G v := by assumption)
  : udensity_at G S v d e₁ e₂ ↔ udensity_at G S v d e₃ e₄ := by
  simp only [udensity_at_iff_ufdensity_at]; apply ufdensity_at_ext; assumption

theorem udensity_at_reach [G.LocallyFinite]
  (r : G.Reachable v u := by assumption) (h : udensity_at G S v d := by assumption)
  (sg : slow_growth_at G v := by assumption) : udensity_at G S u d := by
  rw [udensity_at_iff_ufdensity_at] at ⊢ h; exact ufdensity_at_reach r








#check div_le_div_iff_of_pos_right
#check Filter.limUnder_eq_iff




  -- constructor <;> intro h
  -- · unfold slow_tiling_at
  --   apply tendsto_of_tendsto_of_tendsto_of_le_of_le
  --     (g := fun r ↦ ((ball G (r + (e₁ + τ.d)) v).ncard : Real) / (ball G (r + e₂) v).ncard)
  --     (h := fun r ↦ ((ball G (r + e₁) v).ncard : Real) / (ball G (r + (e₂ + τ.d)) v).ncard)
  --   · sorry
  --   · rw [←slow_growth_at, slow_growth_at_ext e₁ e₂ _ _]
  --     · exact h
  --     · by_contra p
  --     · sorry
  --   · sorry
  --   · sorry
  -- · sorry






  sorry


#check tendsto_of_tendsto_of_tendsto_of_le_of_le
theorem ufdensity_at_tiling [G.LocallyFinite] (π : Policy V) (τ : Tiling G)
  (d : Real) (h : ∀ t, ∑ x ∈ {v | τ.f v = t}.toFinset, π.f x = d / τ.n)
  (v : V) (sg : slow_growth_at G v)
  : ufdensity_at G π v d := by
  rw [ufdensity_at_ext τ.d τ.d]
  unfold ufdensity_at
  apply le_antisymm
  · apply le_trans (b := Filter.limsup (fun r ↦
      (∑ x ∈ (cball τ (r + τ.d) v).toFinset, π.f x) / ↑(cball τ (r + 0) v).ncard) Filter.atTop)
    · sorry
    · apply le_of_eq
      -- rw [←utufdensity_at]
      sorry
  · sorry
