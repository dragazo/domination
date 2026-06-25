import Mathlib

notation "N(" G ", " v ")" => SimpleGraph.neighborSet G v
notation "N[" G ", " v "]" => insert v N(G, v)
notation A "∆" B => symmDiff A B

variable {V : Type*} (G : SimpleGraph V)

----------------------------------------------------------------------------------------------------

def at_least (k : Nat) (S : Set V) := match k with
  | 0 => True
  | k' + 1 => ∃ x, x ∈ S ∧ at_least k' (S \ {x})

theorem at_least_subset {k : Nat} {S T : Set V} : S ⊆ T → at_least k S → at_least k T :=
  k.recOn
  (fun _ _ _ _ ↦ trivial)
  (fun _ ih _ _ s ⟨_, a, b⟩ ↦ ⟨_, s a, ih _ _ (Set.diff_subset_diff_left s) b⟩)
  S T

theorem at_least_le {k₁ k₂ : Nat} {S : Set V} : k₁ ≤ k₂ → at_least k₂ S → at_least k₁ S :=
  Nat.leRec (fun h ↦ h) (fun _ _ ih ⟨_, _, p⟩ ↦ ih (at_least_subset Set.diff_subset p))

theorem at_least_union {k : Nat} {S T : Set V} :
  at_least k (S ∪ T) → ∃ k₁ k₂, k = k₁ + k₂ ∧ at_least k₁ S ∧ at_least k₂ T :=
  k.recOn
  (fun _ _ _ ↦ ⟨0, 0, rfl, trivial, trivial⟩)
  (fun _ ih _ _ ⟨x, p, h⟩ ↦ have ⟨k₁, k₂, a, b, c⟩ := ih _ _ (Set.union_diff_distrib ▸ h); p.elim
    (fun l ↦ ⟨k₁ + 1, k₂, by omega, ⟨x, l, b⟩, at_least_subset Set.diff_subset c⟩)
    (fun r ↦ ⟨k₁, k₂ + 1, by omega, at_least_subset Set.diff_subset b, ⟨x, r, c⟩⟩))
  S T

theorem at_least_union_ph {k : Nat} {S T : Set V} :
  at_least (2 * k + 1) (S ∪ T) → at_least (k + 1) S ∨ at_least (k + 1) T :=
  fun h ↦ have ⟨k₁, k₂, p, q, r⟩ := at_least_union h; (Nat.lt_or_ge k₁ (k + 1)).elim
    (fun _ ↦ (Nat.lt_or_ge k₂ (k + 1)).elim
      (fun _ ↦ by omega)
      (fun y ↦ Or.inr (at_least_le y r)))
    (fun x ↦ Or.inl (at_least_le x q))

----------------------------------------------------------------------------------------------------

def pointwise (P : V → Prop) := ∀ v, P v
def pairwise (P : V → V → Prop) := ∀ u v, u ≠ v → P u v

----------------------------------------------------------------------------------------------------

def open_dom (k : Nat) (S : Set V) (v : V) := at_least k (N(G, v) ∩ S)
def closed_dom (k : Nat) (S : Set V) (v : V) := at_least k (N[G, v] ∩ S)

----------------------------------------------------------------------------------------------------

def open_dist (k : Nat) (S : Set V) (u v : V) := at_least k ((N(G, u) ∆ N(G, v)) ∩ S)
def closed_dist (k : Nat) (S : Set V) (u v : V) := at_least k ((N[G, u] ∆ N[G, v]) ∩ S)
def self_dist (k : Nat) (S : Set V) (u v : V) := at_least k (((N(G, u) ∆ N(G, v)) ∪ {u, v}) ∩ S)

----------------------------------------------------------------------------------------------------

def sharp_open_dist (k : Nat) (S : Set V) (u v : V) :=
  at_least k ((N(G, u) \ N(G, v)) ∩ S) ∨ at_least k ((N(G, v) \ N(G, u)) ∩ S)
def sharp_closed_dist (k : Nat) (S : Set V) (u v : V) :=
  at_least k ((N[G, u] \ N[G, v]) ∩ S) ∨ at_least k ((N[G, v] \ N[G, u]) ∩ S)

----------------------------------------------------------------------------------------------------

def odom (S : Set V) := pointwise (open_dom G 1 S)
def old (S : Set V) := pointwise (open_dom G 1 S) ∧ pairwise (open_dist G 1 S)
def redold (S : Set V) := pointwise (open_dom G 2 S) ∧ pairwise (open_dist G 2 S)
def detold (S : Set V) := pointwise (open_dom G 2 S) ∧ pairwise (sharp_open_dist G 2 S)
def errold (S : Set V) := pointwise (open_dom G 3 S) ∧ pairwise (open_dist G 3 S)

----------------------------------------------------------------------------------------------------

@[simp] theorem inter_inter_disjoint_of_disjoint {α : Type u} (s t w : Set α) (h : Disjoint s t) :
  Disjoint (s ∩ w) (t ∩ w) := by
  intro x
  simp only [Set.le_eq_subset, Set.subset_inter_iff, Set.bot_eq_empty, Set.subset_empty_iff]
  rw [Set.eq_empty_iff_forall_notMem]
  intro ⟨a, _⟩ ⟨b, _⟩ _ c
  exact (Set.disjoint_iff_forall_ne.mp h) (a c) (b c) rfl

@[simp] theorem ncard_div_nonneg {α : Type u} (s t : Set α) :
  0 ≤ (s.ncard : Real) / (t.ncard : Real) := by simp [div_nonneg]

----------------------------------------------------------------------------------------------------

def ball (r : Nat) (v : V) : Set V := { u | G.edist u v ≤ r }
def sphere (r : Nat) (v : V) : Set V := { u | G.edist u v = r }

theorem ball_eq_union_ball (v : V) (r : Nat) : (ball G (r + 1) v) = ⋃ u ∈ N[G, v], ball G r u := by
  ext x; constructor <;> simp only [ball, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion] <;> intro h
  · rw [SimpleGraph.edist_comm] at h; have ⟨W_vx, L_vx⟩ := SimpleGraph.exists_walk_of_edist_ne_top
      (ne_top_of_le_ne_top (fun _ ↦ by contradiction) h)
    cases W_vx with
    | nil => simp
    | @cons v w x A_vw W_wx => exact Or.inr ⟨w, A_vw, by
        rw [SimpleGraph.Walk.length_cons] at L_vx
        rw [←L_vx, ENat.coe_le_coe, Nat.add_le_add_iff_right, ←ENat.coe_le_coe] at h
        exact le_trans (SimpleGraph.edist_comm ▸ (SimpleGraph.edist_le W_wx)) h⟩
  · rw [Nat.cast_add]; match h with
    | Or.inl h => exact le_trans h le_self_add
    | Or.inr ⟨i, A_vi, D_xi⟩ =>
      apply le_trans (b := G.edist x i + G.edist i v) SimpleGraph.edist_triangle
      apply add_le_add D_xi
      rw [SimpleGraph.edist_comm, SimpleGraph.edist_eq_one_iff_adj.mpr A_vi, Nat.cast_one]

theorem ball_eq_ball_sphere (v : V) (r : Nat) :
  (ball G (r + 1) v) = (ball G r v) ∪ (sphere G (r + 1) v) := by
  ext x; simp only [ball, sphere, Set.mem_setOf_eq, Set.mem_union]
  cases G.edist x v with
  | top => exact ⟨fun h ↦ by contradiction, fun h ↦ h.elim (by simp) (fun h ↦ by contradiction)⟩
  | coe d => norm_cast; omega

theorem sphere_eq_ball_sub (v : V) (r : Nat) :
  sphere G (r + 1) v = (ball G (r + 1) v) \ (ball G r v) := by
  ext x; simp only [ball, sphere, Set.mem_setOf_eq, Set.mem_diff]
  cases G.edist x v with
  | top => exact ⟨fun h ↦ by contradiction, fun ⟨h, g⟩ ↦ by contradiction⟩
  | coe d => norm_cast; omega

@[simp] theorem ball_sphere_disjoint (v : V) (r : Nat) :
  Disjoint (ball G r v) (sphere G (r + 1) v) := by
  intro s; simp only [Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]; intro a b
  rw [Set.eq_empty_iff_forall_notMem]; intro x h
  have g := h; apply a at h; apply b at g; simp only [ball, sphere, Set.mem_setOf_eq] at h g
  cases hd : G.edist x v with
  | top => rw [hd] at h; contradiction
  | coe d => rw [hd] at h g; norm_cast at h g; simp [g] at h

noncomputable instance [G.LocallyFinite] (r : Nat) (v : V) : Fintype ↑(ball G r v) := by
  apply Set.Finite.fintype
  induction r generalizing v with
  | zero => simp [ball]
  | succ r ih => rw [ball_eq_union_ball]; exact
    Set.Finite.biUnion (Set.finite_insert.mpr (Set.toFinite _)) (fun i h ↦ ih i)
@[simp] theorem ball_finite [G.LocallyFinite] (v : V) (r : Nat) : (ball G r v).Finite :=
  (ball G r v).toFinite

noncomputable instance [G.LocallyFinite] (r : Nat) (v : V) : Fintype ↑(sphere G r v) := by
  apply Set.Finite.fintype; apply Set.Finite.subset (s := ball G r v) (by simp)
  rw [ball, sphere, Set.setOf_subset_setOf]; aesop
@[simp] theorem sphere_finite [G.LocallyFinite] (v : V) (r : Nat) : (sphere G r v).Finite :=
  (sphere G r v).toFinite

@[simp] theorem ball_subset (v : V) (r e : Nat) : ball G r v ⊆ ball G (r + e) v := by
  induction e with
  | zero => simp
  | succ e ih => apply subset_trans ih; simp [←add_assoc, ball_eq_union_ball]
@[simp] theorem ball_subset' (v : V) (r₁ r₂ : Nat) (h : r₁ ≤ r₂) : ball G r₁ v ⊆ ball G r₂ v := by
  have ⟨k, hk⟩ := Nat.exists_eq_add_of_le h; simp [ball_subset, hk]
@[simp] theorem ball_subset'' [G.LocallyFinite] (v : V) (r₁ r₂ : Nat) (h : r₁ ≤ r₂) :
  (ball G r₁ v).ncard ≤ (ball G r₂ v).ncard := by apply Set.ncard_le_ncard <;> aesop

@[simp] theorem ball_nonempty (v : V) (r : Nat) : (ball G r v).Nonempty :=
  Set.nonempty_of_mem (x := v) (by simp [ball])
@[simp] theorem ball_ne_empty (v : V) (r : Nat) : (ball G r v) ≠ ∅ :=
  Set.Nonempty.ne_empty (by simp)

@[simp] theorem ball_ncard_ne_zero [G.LocallyFinite] (v : V) (r : Nat) : (ball G r v).ncard ≠ 0 :=
  Set.ncard_ne_zero_of_mem (a := v) (by simp [ball])
@[simp] theorem ball_ncard_positive [G.LocallyFinite] (v : V) (r : Nat) : 0 < (ball G r v).ncard :=
  Nat.pos_of_ne_zero (by simp)

----------------------------------------------------------------------------------------------------

def slow_growth_at [G.LocallyFinite] (v : V) (e₁ := 1) (e₂ := 0) := Filter.Tendsto
  (fun r ↦ ((ball G (r + e₁) v).ncard : Real) / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 1)

def slow_boundary_at [G.LocallyFinite] (v : V) (e₁ e₂ : Nat := 0) := Filter.Tendsto
  (fun r ↦ ((sphere G (r + e₁) v).ncard : Real)  / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 0)

structure Policy (V : Type*) where
  f : V → Real
  m : Real := 1
  hm : 0 < m := by aesop
  f0 : ∀ r, 0 ≤ f r := by aesop
  fm : ∀ r, f r ≤ m := by aesop

noncomputable def Policy₀₁ {V : Type*} (S : Set V) : Policy V := {
  f := fun v ↦ have := Classical.propDecidable (v ∈ S); if v ∈ S then 1 else 0
}

def ufdensity_at [G.LocallyFinite] (π : Policy V) (v : V) (d : Real) (e₁ e₂ := 0) := Filter.limsup
  (fun r ↦ (∑ x ∈ (ball G (r + e₁) v), π.f x) / ↑(ball G (r + e₂) v).ncard) Filter.atTop = d

def udensity_at [G.LocallyFinite] (S : Set V) (v : V) (d : Real) (e₁ e₂ := 0) := Filter.limsup
  (fun r ↦ (((ball G (r + e₁) v) ∩ S).ncard : Real) / ↑(ball G (r + e₂) v).ncard) Filter.atTop = d

----------------------------------------------------------------------------------------------------

-- todo: come back later and see if we can prove this without induction
theorem slow_growth_at_ext {G : SimpleGraph V} [G.LocallyFinite] {v : V} {e₁ e₂ : Nat}
  (e₃ := 1) (e₄ := 0) (h₁₂ : e₁ ≠ e₂ := by omega) (h₃₄ : e₃ ≠ e₄ := by omega)
  : slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v e₃ e₄ := by
  let rec helper : ∀ e₁ e₂, e₂ < e₁ → (slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v)
  | 0, _, _ => by contradiction
  | e₁ + 1, e₂ + 1, _ => by
    simp_rw [←helper e₁ e₂ (by omega), slow_growth_at, add_comm e₁, add_comm e₂, ←add_assoc]
    nth_rw 2 [←Filter.tendsto_add_atTop_iff_nat 1]
  | e₁ + 1, 0, _ => by
    cases Decidable.em (e₁ = 0) with | inl h => simp [h] | inr _ =>
    rw [←helper e₁ 0 (by omega)]; unfold slow_growth_at; constructor <;> intro h
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun r ↦ 1) (by simp) h
        (by simp [Pi.le_def, one_le_div]) (by simp [Pi.le_def, div_le_div_iff_of_pos_right])
    · conv => arg 1; ext r; rw [←div_mul_div_cancel₀ (b := ↑(ball G (r + 1) v).ncard) (by simp)]
      conv => arg 3; rw [show (1 : Real) = 1 * 1 by simp]
      apply Filter.Tendsto.mul
      · simp_rw [add_comm e₁, ←add_assoc]; rw [←Filter.tendsto_add_atTop_iff_nat 1] at h; exact h
      · rw [←slow_growth_at] at ⊢ h; rw [helper e₁ 0 (by omega)] at h; exact h
  have assistant : ∀ e₁ e₂, e₁ ≠ e₂ → (slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v) := by
    have t : ∀ e₁ e₂, slow_growth_at G v e₁ e₂ → slow_growth_at G v e₂ e₁ := fun e₁ e₂ h ↦ by
      rw [slow_growth_at]
      conv => arg 1; ext r; rw [show ∀ a b : Real, a / b = (b / a)⁻¹ by intros; simp]
      conv => arg 3; rw [show (1 : Real) = 1⁻¹ by simp]
      exact Filter.Tendsto.inv₀ h (by simp)
    intro e₁ e₂ _; cases Decidable.em (e₂ < e₁) with | inl h => exact helper e₁ e₂ h | inr h =>
    rw [←helper e₂ e₁ (by omega)]; constructor <;> exact fun h ↦ t _ _ h
  rw [assistant _ _ h₁₂, assistant _ _ h₃₄]

@[aesop unsafe]
theorem slow_growth_at_reach {G : SimpleGraph V} [G.LocallyFinite] {u v : V}
  (r : G.Reachable v u := by assumption) (sg : slow_growth_at G v := by assumption)
  : slow_growth_at G u := by
  have helper (v u : V) (r₁ r₂ : Nat) (Avu : G.Adj v u) :
    ((ball G r₁ v).ncard : Real) / ((ball G (r₂ + 1) v).ncard : Real) ≤
    ((ball G (r₁ + 1) u).ncard : Real) / ((ball G r₂ u).ncard : Real) := by
    apply div_le_div₀ (by simp) _ (by simp) <;> norm_cast <;> apply Set.ncard_le_ncard _ (by simp)
    <;> rw [ball_eq_union_ball] <;> exact Set.subset_biUnion_of_mem (by simp [Avu, Avu.symm])
  have ⟨Wvu⟩ := r; induction Wvu with | nil => assumption | @cons v w u Avw Wwu ih =>
  apply ih ⟨Wwu⟩; rw [slow_growth_at_ext 4 1]; apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((slow_growth_at_ext 3 2).mp sg) ((slow_growth_at_ext 5).mp sg)
    <;> simp [Pi.le_def, helper, Avw, Avw.symm]

theorem slow_growth_at_all {G : SimpleGraph V} [G.LocallyFinite] {v : V}
  (c : G.Preconnected := by assumption) (sg : slow_growth_at G v := by assumption)
  : ∀ u, slow_growth_at G u := by aesop

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
        arg 1; ext r;
        rw [←add_assoc, sphere_eq_ball_sub, Set.ncard_diff (by simp) (by simp)]
        rw [Nat.cast_sub (by simp), sub_div, add_assoc]
      rw [←sub_self 1]; apply Filter.Tendsto.sub h; rw [←slow_growth_at] at ⊢ h
      cases e₁ with | zero => simp [slow_growth_at] | succ e₁ =>
      rw [slow_growth_at_ext (e₁ + 1 + 1)]
      exact h
    · conv =>
        arg 1; ext r;
        rw [←add_assoc, ball_eq_ball_sphere, Set.ncard_union_eq (by simp), Nat.cast_add, add_div]
      conv => arg 3; rw [←add_zero 1]
      apply Filter.Tendsto.add _ h; rw [←slow_growth_at]
      cases e₁ with | zero => simp [slow_growth_at] | succ e₁ =>
      rw [slow_growth_at_iff_slow_boundary_at v (e₁ + 1) 0 (by omega)]
      have t := tendsto_of_tendsto_of_tendsto_of_le_of_le (α := Real)
        (g := fun r ↦ 0) (by simp) h (by simp [Pi.le_def])
        (f := fun r ↦ ↑(sphere G (r + e₁ + 1 + 1) v).ncard / ↑(ball G (r + 1) v).ncard)
        (by simp [Pi.le_def, ←add_assoc, div_le_div_of_nonneg_left])
      simp_rw [show ∀ r : Nat, r + e₁ + 1 + 1 = r + 1 + e₁ + 1 by intro; ring] at t
      rw [Filter.tendsto_add_atTop_iff_nat 1 (α := Real)
        (f := fun r ↦ ↑(sphere G (r + e₁ + 1) v).ncard / ↑(ball G r v).ncard)] at t
      exact t

theorem limsup_mul_eq {f g : Nat → Real}
  (l₁ : Filter.Tendsto f Filter.atTop (nhds y₁)) (l₂ : Filter.limsup g Filter.atTop = y₂)
  (p₁ : ∀ r, 0 ≤ f r) (p₂ : ∀ r, 0 ≤ g r)
  (b₁ : ∀ᶠ r in Filter.atTop, f r ≤ m₁) (b₂ : ∀ᶠ r in Filter.atTop, g r ≤ m₂) :
  Filter.limsup (f * g) Filter.atTop = y₁ * y₂ := by
  apply le_antisymm
  · rw [←Filter.Tendsto.limsup_eq l₁, ←l₂]; apply limsup_mul_le _ (by exists m₁) _ (by exists m₂)
    · rw [Filter.frequently_atTop]; intro r; exists r; simp [p₁]
    · rw [Filter.EventuallyLE, Filter.eventually_atTop]; simp [p₂]
  · rw [mul_comm y₁, ←Filter.Tendsto.liminf_eq l₁, ←l₂, mul_comm f]
    apply le_limsup_mul _ (by exists m₂) _ (by exists m₁)
    · rw [Filter.frequently_atTop]; intro r; exists r; simp [p₂]
    · rw [Filter.EventuallyLE, Filter.eventually_atTop]; simp [p₁]

theorem eventually_le_of_slow_growth_at {G : SimpleGraph V} [G.LocallyFinite]
  (e₁ e₂ : Nat) (ε : Real := 1) (hε : 0 < ε := by simp) (sg : slow_growth_at G v := by assumption)
  : ∀ᶠ r in Filter.atTop, ((ball G (r + e₁) v).ncard : ℝ) / (ball G (r + e₂) v).ncard ≤ 1 + ε := by
  apply Filter.Tendsto.eventually_le_const (v := 1) (by simp [hε])
  cases Decidable.em (e₁ = e₂) with | inl h => simp [h] | inr h =>
  rw [←slow_growth_at, slow_growth_at_ext]; exact sg

@[simp] theorem fball_nonneg [G.LocallyFinite] {π : Policy V}
  : 0 ≤ ∑ x ∈ ball G r v, π.f x := by simp [Finset.sum_nonneg, π.f0]

@[simp] theorem fball_div_nonneg [G.LocallyFinite] {π : Policy V}
  : 0 ≤ (∑ x ∈ ball G r₁ v, π.f x) / ↑(ball G r₂ v).ncard := by simp [div_nonneg]

@[simp] theorem fball_div_le_one [G.LocallyFinite] (h : r₁ ≤ r₂)
  : ((ball G r₁ v).ncard : Real) / ↑(ball G r₂ v).ncard ≤ 1 := by
  simp [div_le_one, Set.ncard_le_ncard, h]

@[simp] theorem fball_le_mball [G.LocallyFinite] {π : Policy V}
  : (∑ x ∈ (ball G r v), π.f x) ≤ π.m * ↑(ball G r v).ncard := by
  rw [Set.ncard_eq_toFinset_card _, mul_comm, ←nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul; simp [π.fm]

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
  have impl e₁ e₂ e₃ e₄ (h : ufdensity_at G π v d e₁ e₂) : ufdensity_at G π v d e₃ e₄ := by
    rw [ufdensity_at, ←Filter.limsup_nat_add _ e₁]; simp_rw [add_assoc]
    rw [ufdensity_at, ←Filter.limsup_nat_add _ e₃] at h; simp_rw [add_assoc, add_comm e₃] at h
    conv_lhs =>
      arg 1; ext r;
      rw [←div_mul_div_cancel₀ (b := ((ball G (r + (e₂ + e₃)) v).ncard : Real)) (by simp), mul_comm]
    conv_rhs => rw [←one_mul d]
    apply limsup_mul_eq (m₁ := 2) (m₂ := π.m + 1) _ h (by simp) (by simp) _ _
    · cases Decidable.em (e₂ + e₃ = e₁ + e₄) with | inl t => simp [t] | inr t =>
      rw [←slow_growth_at, slow_growth_at_ext]; exact sg
    · apply Filter.Tendsto.eventually_le_const (v := 1) (by simp)
      cases Decidable.em (e₂ + e₃ = e₁ + e₄) with | inl t => simp [t] | inr t =>
      rw [←slow_growth_at, slow_growth_at_ext]; exact sg
    · apply fball_div_eventually_le <;> aesop
  constructor <;> apply impl

@[aesop unsafe]
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
    apply div_le_div₀ (by simp) _ (by simp)
    · norm_cast; apply Set.ncard_le_ncard _ (by simp); rw [ball_eq_union_ball]
      exact Set.subset_biUnion_of_mem (by simp [Avu])
    · apply Finset.sum_le_sum_of_subset_of_nonneg _ (by simp [π.f0])
      rw [Set.subset_toFinset, Set.coe_toFinset, ball_eq_union_ball]
      exact Set.subset_biUnion_of_mem (by simp [Avu.symm])
  rw [ufdensity_at_ext 1 1]; apply le_antisymm
  · apply le_trans (b := Filter.limsup
      (fun r ↦ (∑ x ∈ ball G (r + 2) v, π.f x) / ↑(ball G (r + 0) v).ncard) Filter.atTop)
      _ (le_of_eq (by rw [←ufdensity_at, ufdensity_at_ext]; exact h))
    apply Filter.limsup_le_limsup
    · apply Filter.Eventually.of_forall; aesop (add safe Avw.symm)
    · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; simp
    · exists π.m + 1; apply fball_div_eventually_le <;> aesop
  · apply le_trans (b := Filter.limsup
      (fun r ↦ (∑ x ∈ ball G (r + 0) v, π.f x) / ↑(ball G (r + 2) v).ncard) Filter.atTop)
      (le_of_eq (Eq.symm (by rw [←ufdensity_at, ufdensity_at_ext]; exact h)))
    apply Filter.limsup_le_limsup
    · apply Filter.Eventually.of_forall; aesop
    · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; simp
    · exists π.m + 1; apply fball_div_eventually_le <;> aesop

theorem ufdensity_at_all {G : SimpleGraph V} [G.LocallyFinite] {π : Policy V} {v : V} {d : Real}
  (c : G.Preconnected := by assumption) (h : ufdensity_at G π v d := by assumption)
  (sg : slow_growth_at G v := by assumption) : ∀ u, ufdensity_at G π u d := by aesop

@[aesop norm simp]
theorem udensity_at_iff_ufdensity_at {G : SimpleGraph V} [G.LocallyFinite] {S : Set V} {v : V}
  {e₁ e₂ : Nat} {d : Real} : udensity_at G S v d e₁ e₂ ↔ ufdensity_at G (Policy₀₁ S) v d e₁ e₂ := by
  unfold ufdensity_at; aesop

theorem udensity_at_ext {G : SimpleGraph V} [G.LocallyFinite] {S : Set V} {v : V} {d : Real}
  {e₁ e₂ : Nat} (e₃ e₄ := 0) (sg : slow_growth_at G v := by assumption)
  : udensity_at G S v d e₁ e₂ ↔ udensity_at G S v d e₃ e₄ := by
  simp only [udensity_at_iff_ufdensity_at]; apply ufdensity_at_ext; assumption

theorem udensity_at_reach {G : SimpleGraph V} [G.LocallyFinite] {S : Set V} {u v : V} {d : Real}
  (r : G.Reachable v u := by assumption) (h : udensity_at G S v d := by assumption)
  (sg : slow_growth_at G v := by assumption) : udensity_at G S u d := by aesop

theorem udensity_at_all {G : SimpleGraph V} [G.LocallyFinite] {S : Set V} {v : V} {d : Real}
  (c : G.Preconnected := by assumption) (h : udensity_at G S v d := by assumption)
  (sg : slow_growth_at G v := by assumption) : ∀ u, udensity_at G S u d := by aesop

structure tiling (G : SimpleGraph V) where
  c : Type*
  f : V → c
  n : Nat
  n0 : n ≠ 0
  d : Nat
  d0 : d ≠ 0
  h₁ : ∀ c, {v | f v = c}.ncard = n
  h₂ : ∀ u v, f u = f v → G.edist u v ≤ d
