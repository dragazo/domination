import Mathlib
import Domination.General

notation "N(" G ", " v ")" => SimpleGraph.neighborSet G v
notation "N[" G ", " v "]" => insert v N(G, v)
notation A "∆" B => symmDiff A B

variable {V : Type*} (G : SimpleGraph V)

----------------------------------------------------------------------------------------------------

def ball (r : Nat) (v : V) : Set V := { u | G.edist u v ≤ r }

theorem ball_nonempty : (ball G r v).Nonempty := by
  apply Set.nonempty_of_mem (x := v); simp [ball]

theorem ball_subset (h : r₁ ≤ r₂) : ball G r₁ v ⊆ ball G r₂ v := by
  intro x hx; rw [ball, Set.mem_setOf_eq] at ⊢ hx; apply le_trans hx; simp [h]

theorem ball_eq_union_ball : (ball G (r + 1) v) = ⋃ u ∈ N[G, v], ball G r u := by
  ext x; constructor <;> simp only [ball, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion] <;> intro h
  · rw [G.edist_comm] at h
    have ⟨Wvx, Lvx⟩ := G.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by tauto) h)
    cases Wvx with | nil => simp | @cons v w x Avw Wwx => exact Or.inr ⟨w, Avw, by
    rw [SimpleGraph.Walk.length_cons] at Lvx
    rw [←Lvx, ENat.coe_le_coe, Nat.add_le_add_iff_right, ←ENat.coe_le_coe] at h
    exact le_trans (G.edist_comm ▸ (G.edist_le Wwx)) h⟩
  · rw [Nat.cast_add]; match h with
    | Or.inl h => exact le_trans h le_self_add | Or.inr ⟨i, Avi, Dxi⟩ =>
    apply le_trans (b := G.edist x i + G.edist i v) G.edist_triangle
    apply add_le_add Dxi
    rw [G.edist_comm, G.edist_eq_one_iff_adj.mpr Avi, Nat.cast_one]

noncomputable instance [G.LocallyFinite] : Fintype (ball G r v) := by
  apply Set.Finite.fintype; induction r generalizing v with | zero => simp [ball] | succ r ih =>
  rw [ball_eq_union_ball]
  exact Set.Finite.biUnion (Set.finite_insert.mpr (Set.toFinite _)) (fun _ _ ↦ ih)

macro "ball!" "[" h:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [
  ball_nonempty, ball_subset,
  Set.toFinite, Set.ncard_le_ncard, Set.ncard_pos, Set.Nonempty.ne_empty,
  Pi.le_def, one_le_div, div_le_one, div_le_div_iff_of_pos_right,
  $h,*
])
macro "ball!" : tactic => `(tactic| ball! [])

----------------------------------------------------------------------------------------------------

def shell (r : Nat) (v : V) : Set V := { u | G.edist u v = r }

theorem ball_eq_ball_shell : (ball G (r + 1) v) = (ball G r v) ∪ (shell G (r + 1) v) := by
  ext x; simp only [ball, shell, Set.mem_setOf_eq, Set.mem_union]
  cases G.edist x v with | top => simp; tauto | coe => norm_cast; omega

theorem shell_eq_ball_sub : shell G (r + 1) v = (ball G (r + 1) v) \ (ball G r v) := by
  ext x; simp only [ball, shell, Set.mem_setOf_eq, Set.mem_diff]
  cases G.edist x v with | top => simp; tauto | coe => norm_cast; omega

theorem ball_shell_disjoint (h : r₁ < r₂) : Disjoint (ball G r₁ v) (shell G r₂ v) := by
  intro s; simp only [Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]; intro a b
  rw [Set.eq_empty_iff_forall_notMem]; intro x hx
  have gx := hx; apply a at hx; apply b at gx; simp only [ball, shell, Set.mem_setOf_eq] at hx gx
  cases hd : G.edist x v with
  | top => rw [hd] at hx; contradiction
  | coe => rw [hd] at hx gx; norm_cast at hx gx; rw [gx, ←not_lt] at hx; contradiction

noncomputable instance [G.LocallyFinite] : Fintype (shell G r v) := by
  apply Set.Finite.fintype; apply Set.Finite.subset (s := ball G r v) (by ball!)
  rw [ball, shell, Set.setOf_subset_setOf]; intros; simp [*]

macro "shell!" "[" h:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [
  ball_shell_disjoint,
  ball_nonempty, ball_subset,
  Set.toFinite, Set.ncard_le_ncard, Set.Nonempty.ne_empty,
  pos_of_ne_zero,
  $h,*
])
macro "shell!" : tactic => `(tactic| shell! [])

----------------------------------------------------------------------------------------------------

structure Tiling where
  t : Type*
  f : V → t
  n : Nat
  d : Nat
  n0 : n ≠ 0 := by norm_num
  d0 : d ≠ 0 := by norm_num
  h₁ : ∀ t, {v | f v = t}.ncard = n := by aesop
  h₂ : ∀ u v, f u = f v → G.edist u v ≤ d := by aesop

noncomputable instance (τ : Tiling G) (t : τ.t) : Fintype {v | τ.f v = t} := by
  apply Set.Finite.fintype; apply Set.finite_of_ncard_ne_zero; rw [τ.h₁ t]; exact τ.n0

def utball {G : SimpleGraph V} (τ : Tiling G) (r : Nat) (v : V) :=
  ⋃ t ∈ {t | ∃ u ∈ {x | τ.f x = t}, u ∈ ball G r v}, {x | τ.f x = t}
def ltball {G : SimpleGraph V} (τ : Tiling G) (r : Nat) (v : V) :=
  ⋃ t ∈ {t | ∀ u ∈ {x | τ.f x = t}, u ∈ ball G r v}, {x | τ.f x = t}

def Tiling.id : Tiling G := { t := V, f := fun v ↦ v, n := 1, d := 1 }

@[simp] theorem Tiling.id.utball_eq : utball (Tiling.id G) r v = ball G r v := by
  rw [utball, ball]; aesop
@[simp] theorem Tiling.id.ltball_eq : ltball (Tiling.id G) r v = ball G r v := by
  rw [ltball, ball]; aesop

----------------------------------------------------------------------------------------------------

theorem utball_nonempty : (utball τ r v).Nonempty := by
  apply Set.nonempty_of_mem (x := v)
  simp only [utball, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right']
  exists v; simp [ball]

theorem utball_subset (h : r₁ ≤ r₂) : utball τ r₁ v ⊆ utball τ r₂ v := by
  intro x hx; simp only [utball, ball,
    Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right'] at ⊢ hx
  obtain ⟨y, hy₁, hy₂⟩ := hx; exists y; apply And.intro hy₁; apply le_trans (b := ↑r₁) <;> simp [*]

theorem utball_lower {G : SimpleGraph V} {τ : Tiling G} : ball G r v ⊆ utball τ r v := by
  simp only [ball, utball, Set.mem_setOf_eq, Set.iUnion_exists]; intro x h; aesop

theorem utball_upper {G : SimpleGraph V} {τ : Tiling G}
  : utball τ r v ⊆ ball G (r + τ.d) v := fun p h ↦ by
  simp only [utball, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right'] at h
  obtain ⟨q, h₁, h₂⟩ := h; apply τ.h₂ at h₁
  simp only [ball, Nat.cast_add, Set.mem_setOf_eq] at ⊢ h₂
  rw [G.edist_comm] at h₁; apply le_trans (b := G.edist p q + G.edist q v)
  · exact G.edist_triangle
  · rw [add_comm]; exact add_le_add h₂ h₁

noncomputable instance [G.LocallyFinite] (τ : Tiling G) : Fintype (utball τ r v) := by
  apply Set.Finite.fintype; exact Set.Finite.subset (ball G _ v).toFinite utball_upper

theorem utball_eq_union_utball {G : SimpleGraph V} {τ : Tiling G}
  : (utball τ (r + 1) v) = ⋃ u ∈ ball G 1 v, utball τ r u := by
  ext x; constructor <;> simp only [utball, Set.mem_setOf_eq, ball, Nat.cast_add, Nat.cast_one,
    Set.iUnion_exists, Set.mem_iUnion, exists_prop, exists_and_right, exists_eq_right',
    forall_exists_index, and_imp]
  · intro y τxy yvd; rw [G.edist_comm] at yvd
    have ⟨vy, vyd⟩ := G.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by tauto) yvd)
    cases vy with
    | nil => exists v; apply And.intro (by simp); exists v; simp [τxy]
    | @cons v w x vw wy =>
      exists w; apply And.intro (by rw [G.adj_comm] at vw; simp [G.edist_le_one_iff_adj_or_eq, vw])
      exists y; apply And.intro τxy; rw [SimpleGraph.Walk.length_cons] at vyd
      rw [←ENat.add_le_add_iff_right (k := 1) (by decide)]; apply le_trans _ yvd
      rw [←vyd, Nat.cast_add, ENat.coe_one, ENat.add_le_add_iff_right (by decide), G.edist_comm]
      apply SimpleGraph.Walk.edist_le
  · intro y yvd z τxz zyd; exists z; apply And.intro τxz
    exact le_trans (b := G.edist z y + G.edist y v) G.edist_triangle (add_le_add zyd yvd)

macro "utball!" "[" h:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [
  utball_nonempty, utball_subset, utball_lower, utball_upper,
  ball_nonempty, ball_subset,
  Set.toFinite, Set.ncard_le_ncard, Set.ncard_pos, Set.Nonempty.ne_empty,
  Pi.le_def, one_le_div, div_le_div_iff_of_pos_right,
  $h,*
])
macro "utball!" : tactic => `(tactic| utball! [])

----------------------------------------------------------------------------------------------------

theorem ltball_subset (h : r₁ ≤ r₂) : ltball τ r₁ v ⊆ ltball τ r₂ v := by
  intro x hx; simp only [ltball, ball,
    Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, exists_eq_right'] at ⊢ hx
  intro u hu; rw [←ENat.coe_le_coe] at h; apply le_trans _ h; apply hx _ hu

theorem ltball_lower {G : SimpleGraph V} {τ : Tiling G}
  : ball G r v ⊆ ltball τ (r + τ.d) v := fun p h ↦ by
  simp only [ball, ltball, Set.mem_setOf_eq] at ⊢ h
  simp only [Set.mem_setOf_eq, Nat.cast_add, Set.mem_iUnion, exists_prop, exists_eq_right']
  intro x hx; apply τ.h₂ at hx; apply le_trans (b := G.edist x p + G.edist p v)
  · exact SimpleGraph.edist_triangle
  · rw [add_comm]; exact add_le_add h hx

theorem ltball_upper {G : SimpleGraph V} {τ : Tiling G}
  : ltball τ r v ⊆ ball G r v := by simp [ltball, ball]

noncomputable instance [G.LocallyFinite] (τ : Tiling G) : Fintype (ltball τ r v) := by
  apply Set.Finite.fintype; apply Set.Finite.subset (ball G r v).toFinite ltball_upper

macro "ltball!" "[" h:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [
  ltball_subset, ltball_lower, ltball_upper,
  ball_nonempty, ball_subset,
  Set.toFinite,
  $h,*
])
macro "ltball!" : tactic => `(tactic| ltball! [])

----------------------------------------------------------------------------------------------------

def slow_growth_at [G.LocallyFinite] (v : V) (e₁ := 1) (e₂ := 0) := Filter.Tendsto
  (fun r ↦ ((ball G (r + e₁) v).ncard : Real) / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 1)

def slow_tiling_at {G : SimpleGraph V} [G.LocallyFinite] (τ : Tiling G) (v : V) (e₁ := 1) (e₂ := 0)
  := Filter.Tendsto
  (fun r ↦ ((utball τ (r + e₁) v).ncard : Real) / ((utball τ (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 1)

def slow_boundary_at [G.LocallyFinite] (v : V) (e₁ e₂ : Nat := 0) := Filter.Tendsto
  (fun r ↦ ((shell G (r + e₁) v).ncard : Real) / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 0)

structure Policy (V : Type*) where
  f : V → Real
  m : Real := 1
  hm : 0 < m := by norm_num
  f₀ : ∀ r, 0 ≤ f r := by aesop
  fₘ : ∀ r, f r ≤ m := by aesop

noncomputable def Policy₀₁ {V : Type*} (S : Set V) : Policy V := {
  f := fun v ↦ have := Classical.propDecidable (v ∈ S); if v ∈ S then 1 else 0
}

def ufdensity_at [G.LocallyFinite] (π : Policy V) (v : V) (d : Real) (e₁ e₂ := 0) := Filter.limsup
  (fun r ↦ (∑ x ∈ (ball G (r + e₁) v), π.f x) / ↑(ball G (r + e₂) v).ncard) Filter.atTop = d

def utufdensity_at {G : SimpleGraph V} [G.LocallyFinite]
  (π : Policy V) (τ : Tiling G) (v : V) (d : Real) (e₁ e₂ : Nat := 0) := Filter.limsup
  (fun r ↦ (∑ x ∈ (utball τ (r + e₁) v), π.f x) / (utball τ (r + e₂) v).ncard) Filter.atTop = d

def udensity_at [G.LocallyFinite] (S : Set V) (v : V) (d : Real) (e₁ e₂ := 0) := Filter.limsup
  (fun r ↦ (((ball G (r + e₁) v) ∩ S).ncard : Real) / ↑(ball G (r + e₂) v).ncard) Filter.atTop = d

----------------------------------------------------------------------------------------------------

-- todo: refractor this to use the tiling ext theorem with a unit tile
theorem slow_growth_at_ext {G : SimpleGraph V} [G.LocallyFinite] {v : V} {e₁ e₂ : Nat}
  (e₃ := 1) (e₄ := 0) (h₁₂ : e₁ ≠ e₂ := by omega) (h₃₄ : e₃ ≠ e₄ := by omega)
  : slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v e₃ e₄ := by
  let rec helper : ∀ e₁ e₂, e₂ < e₁ → (slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v)
  | 0, _, _ => by contradiction
  | e₁ + 1, e₂ + 1, _ => by
    simp_rw [←helper e₁ e₂ (by omega), slow_growth_at, add_comm e₁, add_comm e₂, ←add_assoc]
    nth_rw 2 [←Filter.tendsto_add_atTop_iff_nat 1]
  | e₁ + 1, 0, _ => by
    cases Decidable.em (e₁ = 0) with | inl t => simp [t] | inr =>
    rw [←helper e₁ 0 (by omega)]; unfold slow_growth_at; constructor <;> intro h
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun r ↦ 1) (by simp) h <;> ball!
    · conv => arg 1; ext r; rw [←div_mul_div_cancel₀ (b := ↑(ball G (r + 1) v).ncard) (by ball!)]
      conv => arg 3; rw [show (1 : Real) = 1 * 1 by simp]
      apply Filter.Tendsto.mul
      · simp_rw [add_comm e₁, ←add_assoc]; rw [←Filter.tendsto_add_atTop_iff_nat 1] at h; exact h
      · rw [←slow_growth_at] at ⊢ h; rw [helper e₁ 0 (by omega)] at h; exact h
  have assistant : ∀ {e₁ e₂}, e₁ ≠ e₂ → (slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v) := by
    have t : ∀ e₁ e₂, slow_growth_at G v e₁ e₂ → slow_growth_at G v e₂ e₁ := fun e₁ e₂ h ↦ by
      unfold slow_growth_at
      conv => arg 1; ext r; rw [show ∀ a b : Real, a / b = (b / a)⁻¹ by intros; simp]
      conv => arg 3; rw [show (1 : Real) = 1⁻¹ by simp]
      exact Filter.Tendsto.inv₀ h (by simp)
    intro e₁ e₂ _; cases Decidable.em (e₂ < e₁) with | inl h => exact helper e₁ e₂ h | inr =>
    rw [←helper e₂ e₁ (by omega)]; constructor <;> apply t
  rw [assistant h₁₂, assistant h₃₄]

theorem slow_growth_at_reach {G : SimpleGraph V} [G.LocallyFinite] {u v : V}
  (r : G.Reachable v u := by assumption) (sg : slow_growth_at G v := by assumption)
  : slow_growth_at G u := by
  have helper (v u : V) (r₁ r₂ : Nat) (Avu : G.Adj v u) :
    ((ball G r₁ v).ncard : Real) / ((ball G (r₂ + 1) v).ncard : Real) ≤
    ((ball G (r₁ + 1) u).ncard : Real) / ((ball G r₂ u).ncard : Real) := by
    apply div_le_div₀ (by simp) _ (by ball!) <;> norm_cast <;> apply Set.ncard_le_ncard _ (by ball!)
    <;> rw [ball_eq_union_ball] <;> exact Set.subset_biUnion_of_mem (by simp [Avu, Avu.symm])
  have ⟨Wvu⟩ := r; induction Wvu with | nil => assumption | @cons v w u Avw Wwu ih =>
  apply ih ⟨Wwu⟩; rw [slow_growth_at_ext 4 1]; apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((slow_growth_at_ext 3 2).mp sg) ((slow_growth_at_ext 5).mp sg)
    <;> simp [Pi.le_def, helper, Avw, Avw.symm]

theorem slow_growth_at_all {G : SimpleGraph V} [G.LocallyFinite] {v : V}
  (c : G.Preconnected := by assumption) (sg : slow_growth_at G v := by assumption)
  : ∀ u, slow_growth_at G u := fun v ↦ slow_growth_at_reach (c _ _)

-- note: e₁ < e₂ is not provable in general by counterexample: tree with #children = depth
theorem slow_growth_at_iff_slow_boundary_at [G.LocallyFinite] (v : V) :
  ∀ e₁ e₂, e₂ < e₁ → (slow_growth_at G v e₁ e₂ ↔ slow_boundary_at G v e₁ e₂)
  | 0, _, _ => by contradiction
  | e₁ + 1, e₂ + 1, _ => by
    have ih := slow_growth_at_iff_slow_boundary_at v e₁ e₂ (by omega)
    simp only [slow_growth_at, slow_boundary_at, add_comm e₁, add_comm e₂, ←add_assoc] at ⊢ ih
    nth_rw 1 [←Filter.tendsto_add_atTop_iff_nat 1] at ih
    nth_rw 2 [←Filter.tendsto_add_atTop_iff_nat 1] at ih; exact ih
  | e₁ + 1, 0, _ => by
    constructor <;> rw [slow_growth_at, slow_boundary_at] <;> intro h
    · conv =>
        arg 1; ext r
        rw [←add_assoc, shell_eq_ball_sub, Set.ncard_diff (by ball!) (by ball!)]
        rw [Nat.cast_sub (by ball!), sub_div, add_assoc]
      rw [←sub_self 1]; apply Filter.Tendsto.sub h; rw [←slow_growth_at] at ⊢ h
      cases e₁ with | zero => ball! [slow_growth_at] | succ e₁ =>
      rw [slow_growth_at_ext (e₁ + 1 + 1)]; exact h
    · conv =>
        arg 1; ext r
        rw [←add_assoc, ball_eq_ball_shell, Set.ncard_union_eq (by shell!), Nat.cast_add, add_div]
      conv => arg 3; rw [←add_zero 1]
      apply Filter.Tendsto.add _ h; rw [←slow_growth_at]
      cases e₁ with | zero => ball! [slow_growth_at] | succ e₁ =>
      rw [slow_growth_at_iff_slow_boundary_at v (e₁ + 1) 0 (by omega)]
      have t := tendsto_of_tendsto_of_tendsto_of_le_of_le (α := Real)
        (g := fun r ↦ 0) (by simp) h (by simp [Pi.le_def, div_nonneg])
        (f := fun r ↦ ↑(shell G (r + e₁ + 1 + 1) v).ncard / ↑(ball G (r + 1) v).ncard)
        (by simp_rw [←add_assoc, Pi.le_def]; intro r; apply div_le_div_of_nonneg_left <;> shell!)
      simp_rw [show ∀ r : Nat, r + e₁ + 1 + 1 = r + 1 + e₁ + 1 by intro; ring] at t
      rw [Filter.tendsto_add_atTop_iff_nat 1 (α := Real)
        (f := fun r ↦ ↑(shell G (r + e₁ + 1) v).ncard / ↑(ball G r v).ncard)] at t
      exact t

theorem eventually_le_of_slow_growth_at {G : SimpleGraph V} [G.LocallyFinite]
  (e₁ e₂ : Nat) (ε : Real := 1) (hε : 0 < ε := by simp) (sg : slow_growth_at G v := by assumption)
  : ∀ᶠ r in Filter.atTop, ((ball G (r + e₁) v).ncard : ℝ) / (ball G (r + e₂) v).ncard ≤ 1 + ε := by
  apply Filter.Tendsto.eventually_le_const (v := 1) (by simp [hε])
  cases Decidable.em (e₁ = e₂) with | inl h => ball! [h] | inr h =>
  rw [←slow_growth_at, slow_growth_at_ext]; exact sg

@[simp] theorem fball_nonneg [G.LocallyFinite] {π : Policy V}
  : 0 ≤ ∑ x ∈ ball G r v, π.f x := by simp [Finset.sum_nonneg, π.f₀]

@[simp] theorem fball_div_nonneg [G.LocallyFinite] {π : Policy V}
  : 0 ≤ (∑ x ∈ ball G r₁ v, π.f x) / ↑(ball G r₂ v).ncard := by simp [div_nonneg]

@[simp] theorem fball_div_le_one [G.LocallyFinite] (h : r₁ ≤ r₂)
  : ((ball G r₁ v).ncard : Real) / ↑(ball G r₂ v).ncard ≤ 1 := by ball! [h]

@[simp] theorem fball_le_mball [G.LocallyFinite] {π : Policy V}
  : (∑ x ∈ (ball G r v), π.f x) ≤ π.m * ↑(ball G r v).ncard := by
  rw [Set.ncard_eq_toFinset_card _, mul_comm, ←nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul; simp [π.fₘ]

@[simp] theorem fball_div_eventually_le [G.LocallyFinite] {π : Policy V}
  (e₁ e₂ : Nat) (ε : Real := 1) (hε : 0 < ε := by simp) (sg : slow_growth_at G v := by assumption)
  : ∀ᶠ (r : Nat) in Filter.atTop,
    (∑ x ∈ (ball G (r + e₁) v), π.f x) / ↑(ball G (r + e₂) v).ncard ≤ π.m + ε := by
  apply Filter.Eventually.mono (eventually_le_of_slow_growth_at e₁ e₂ (ε / π.m) (div_pos hε π.hm))
  intro r q; apply le_trans (b := π.m * (↑(ball G (r + e₁) v).ncard / ↑(ball G (r + e₂) v).ncard))
  · rw [mul_div]; apply div_le_div_of_nonneg_right _ (by simp); simp
  · conv_rhs => rw [←mul_one π.m, ←mul_div_cancel₀ ε (ne_of_lt π.hm).symm, ←mul_add]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt π.hm); exact q

@[simp] theorem Policy₀₁.sum_eq_ncard (S s : Set V) [Fintype ↑s]
  : ∑ x ∈ s, (Policy₀₁ S).f x = (s ∩ S).ncard := by simp [Policy₀₁, ←Set.ncard_coe_finset]

theorem ufdensity_at_ext {G : SimpleGraph V} [G.LocallyFinite] {π : Policy V} {v : V} {d : Real}
  {e₁ e₂ : Nat} (e₃ e₄ := 0) (sg : slow_growth_at G v := by assumption)
  : ufdensity_at G π v d e₁ e₂ ↔ ufdensity_at G π v d e₃ e₄ := by
  suffices h : ∀ e₁ e₂ e₃ e₄, ufdensity_at G π v d e₁ e₂ → ufdensity_at G π v d e₃ e₄ by aesop
  intro e₁ e₂ e₃ e₄ h
  rw [ufdensity_at, ←Filter.limsup_nat_add _ e₁]; simp_rw [add_assoc]
  rw [ufdensity_at, ←Filter.limsup_nat_add _ e₃] at h; simp_rw [add_assoc, add_comm e₃] at h
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

theorem ufdensity_at_reach {G : SimpleGraph V} [G.LocallyFinite] {π : Policy V} {u v : V} {d : Real}
  (r : G.Reachable v u := by assumption) (h : ufdensity_at G π v d := by assumption)
  (sg : slow_growth_at G v := by assumption)
  : ufdensity_at G π u d := by
  have ⟨Wvu⟩ := r; induction Wvu with | nil => assumption | @cons v w u Avw Wwu ih =>
  apply ih ⟨Wwu⟩ _ (slow_growth_at_reach (SimpleGraph.Adj.reachable Avw))
  have sgw : slow_growth_at G w := slow_growth_at_reach (SimpleGraph.Adj.reachable Avw)
  have helper (v u : V) (r₁ r₂ : Nat) (Avu : G.Adj v u) :
    (∑ x ∈ ball G r₁ v, π.f x) / (ball G (r₂ + 1) v).ncard ≤
    (∑ x ∈ ball G (r₁ + 1) u, π.f x) / (ball G r₂ u).ncard := by
    apply div_le_div₀ (by simp) _ (by ball!)
    · norm_cast; apply Set.ncard_le_ncard _ (by ball!); rw [ball_eq_union_ball]
      exact Set.subset_biUnion_of_mem (by simp [Avu])
    · apply Finset.sum_le_sum_of_subset_of_nonneg _ (by simp [π.f₀])
      rw [Set.subset_toFinset, Set.coe_toFinset, ball_eq_union_ball]
      exact Set.subset_biUnion_of_mem (by simp [Avu.symm])
  rw [ufdensity_at_ext 1 1]; apply le_antisymm
  · apply le_trans (b := Filter.limsup
      (fun r ↦ (∑ x ∈ ball G (r + 2) v, π.f x) / ↑(ball G (r + 0) v).ncard) Filter.atTop)
      _ (le_of_eq (by rw [←ufdensity_at, ufdensity_at_ext]; exact h))
    apply Filter.limsup_le_limsup
    · apply Filter.Eventually.of_forall; simp [*, Avw.symm]
    · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; simp
    · exists π.m + 1; apply fball_div_eventually_le <;> simp [*]
  · apply le_trans (b := Filter.limsup
      (fun r ↦ (∑ x ∈ ball G (r + 0) v, π.f x) / ↑(ball G (r + 2) v).ncard) Filter.atTop)
      (le_of_eq (Eq.symm (by rw [←ufdensity_at, ufdensity_at_ext]; exact h)))
    apply Filter.limsup_le_limsup
    · apply Filter.Eventually.of_forall; simp [*]
    · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; simp
    · exists π.m + 1; apply fball_div_eventually_le <;> simp [*]

theorem ufdensity_at_all {G : SimpleGraph V} [G.LocallyFinite] {π : Policy V} {v : V} {d : Real}
  (c : G.Preconnected := by assumption) (h : ufdensity_at G π v d := by assumption)
  (sg : slow_growth_at G v := by assumption)
  : ∀ u, ufdensity_at G π u d := fun v ↦ ufdensity_at_reach (c _ _)

theorem udensity_at_iff_ufdensity_at {G : SimpleGraph V} [G.LocallyFinite] {S : Set V} {v : V}
  {e₁ e₂ : Nat} {d : Real} : udensity_at G S v d e₁ e₂ ↔ ufdensity_at G (Policy₀₁ S) v d e₁ e₂ := by
  simp [udensity_at, ufdensity_at]

theorem udensity_at_ext {G : SimpleGraph V} [G.LocallyFinite] {S : Set V} {v : V} {d : Real}
  {e₁ e₂ : Nat} (e₃ e₄ := 0) (sg : slow_growth_at G v := by assumption)
  : udensity_at G S v d e₁ e₂ ↔ udensity_at G S v d e₃ e₄ := by
  simp only [udensity_at_iff_ufdensity_at]; apply ufdensity_at_ext; assumption

theorem udensity_at_reach {G : SimpleGraph V} [G.LocallyFinite] {S : Set V} {u v : V} {d : Real}
  (r : G.Reachable v u := by assumption) (h : udensity_at G S v d := by assumption)
  (sg : slow_growth_at G v := by assumption) : udensity_at G S u d := by
  rw [udensity_at_iff_ufdensity_at] at ⊢ h; exact ufdensity_at_reach r

theorem udensity_at_all {G : SimpleGraph V} [G.LocallyFinite] {S : Set V} {v : V} {d : Real}
  (c : G.Preconnected := by assumption) (h : udensity_at G S v d := by assumption)
  (sg : slow_growth_at G v := by assumption)
  : ∀ u, udensity_at G S u d := fun v ↦ udensity_at_reach (c _ _)

theorem slow_tiling_at_ext {G : SimpleGraph V} [G.LocallyFinite] {τ : Tiling G}
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
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun r ↦ 1) (by simp) h <;> utball!
    · conv =>
        arg 1; ext r; rw [←div_mul_div_cancel₀ (b := ↑(utball τ (r + 1) v).ncard) (by utball!)]
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

theorem slow_growth_at_iff_slow_tiling_at {G : SimpleGraph V} [G.LocallyFinite] {τ : Tiling G}
  (h₁₂ : e₁ ≠ e₂) : slow_growth_at G v e₁ e₂ ↔ slow_tiling_at τ v e₁ e₂ := by
  constructor <;> intro h
  · unfold slow_tiling_at; apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun r ↦ ((ball G (r + e₁) v).ncard : Real) / (ball G (r + e₂ + τ.d) v).ncard)
      (h := fun r ↦ ((ball G (r + e₁ + τ.d) v).ncard : Real) / (ball G (r + e₂) v).ncard)
    · simp_rw [add_assoc]; rw [←slow_growth_at]
      cases Decidable.em (e₁ = e₂ + τ.d) with | inl t => ball! [t, slow_growth_at] | inr =>
      rw [slow_growth_at_ext e₁ e₂]; exact h
    · simp_rw [add_assoc]; rw [←slow_growth_at]
      cases Decidable.em ((e₁ + τ.d) = e₂) with | inl t => ball! [t, slow_growth_at] | inr =>
      rw [slow_growth_at_ext e₁ e₂]; exact h
    all_goals rw [Pi.le_def]; intro r; apply div_le_div₀ <;> utball!
  · unfold slow_growth_at; rw [←Filter.tendsto_add_atTop_iff_nat τ.d]
    simp_rw [add_assoc, add_comm τ.d, ←add_assoc]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun r ↦ ((utball τ (r + e₁) v).ncard : Real) / (utball τ (r + e₂ + τ.d) v).ncard)
      (h := fun r ↦ ((utball τ (r + e₁ + τ.d) v).ncard : Real) / (utball τ (r + e₂) v).ncard)
    · simp_rw [add_assoc]; rw [←slow_tiling_at]
      cases Decidable.em (e₁ = e₂ + τ.d) with | inl t => utball! [t, slow_tiling_at] | inr =>
      rw [slow_tiling_at_ext e₁ e₂]; exact h
    · simp_rw [add_assoc]; rw [←slow_tiling_at]
      cases Decidable.em (e₁ + τ.d = e₂) with | inl t => utball! [t, slow_tiling_at] | inr =>
      rw [slow_tiling_at_ext e₁ e₂]; exact h
    all_goals rw [Pi.le_def]; intro r; apply div_le_div₀ <;> utball!


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



theorem utufdensity_at_ext {G : SimpleGraph V} [G.LocallyFinite]
  {π : Policy V} {τ : Tiling G} {v : V} {e₁ e₂ : Nat} (e₃ e₄ : Nat := 0)
  : utufdensity_at π τ v d e₁ e₂ ↔ utufdensity_at π τ v d e₃ e₄ := by
  suffices ∀ e₁ e₂ e₃ e₄, utufdensity_at π τ v d e₁ e₂ → utufdensity_at π τ v d e₃ e₄ by aesop
  intro e₁ e₂ e₃ e₄ h
  unfold utufdensity_at


  sorry


#check tendsto_of_tendsto_of_tendsto_of_le_of_le
theorem ufdensity_at_tiling {G : SimpleGraph V} [G.LocallyFinite] (π : Policy V) (τ : Tiling G)
  (d : Real) (h : ∀ t, ∑ x ∈ {v | τ.f v = t}.toFinset, π.f x = d / τ.n)
  (v : V) (sg : slow_growth_at G v)
  : ufdensity_at G π v d := by
  rw [ufdensity_at_ext τ.d τ.d]
  unfold ufdensity_at
  apply le_antisymm
  · apply le_trans (b := Filter.limsup (fun r ↦
      (∑ x ∈ (utball τ (r + τ.d) v).toFinset, π.f x) / ↑(utball τ (r + 0) v).ncard) Filter.atTop)
    · sorry
    · apply le_of_eq
      -- rw [←utufdensity_at]
      sorry
  · sorry
