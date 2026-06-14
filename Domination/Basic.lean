import Mathlib

notation "N(" G ", " v ")" => SimpleGraph.neighborSet G v
notation "N[" G ", " v "]" => insert v N(G, v)
notation A "∆" B => symmDiff A B

universe u
variable {V : Type u} (G : SimpleGraph V)

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

@[simp] theorem ball_subset (v : V) (r e : Nat) : ball G r v ⊆ ball G (r + e) v := by
  induction e with
  | zero => simp
  | succ e ih => apply subset_trans ih; simp [←add_assoc, ball_eq_union_ball]

noncomputable instance [G.LocallyFinite] (r : Nat) (v : V) : Finite (ball G r v) := by
  apply Set.Finite.to_subtype
  induction r generalizing v with
  | zero => simp [ball]
  | succ r ih => rw [ball_eq_union_ball]; exact
    Set.Finite.biUnion (Set.finite_insert.mpr (Set.toFinite _)) (fun i h ↦ ih i)
@[simp] theorem ball_finite [G.LocallyFinite] (v : V) (r : Nat) : (ball G r v).Finite :=
  (ball G r v).toFinite

noncomputable instance [G.LocallyFinite] (r : Nat) (v : V) : Finite (sphere G r v) := by
  apply Set.Finite.to_subtype; apply Set.Finite.subset (s := ball G r v) (by simp)
  rw [ball, sphere, Set.setOf_subset_setOf]; aesop
@[simp] theorem sphere_finite [G.LocallyFinite] (v : V) (r : Nat) : (sphere G r v).Finite :=
  (sphere G r v).toFinite

@[simp] theorem ball_nonempty (v : V) (r : Nat) : (ball G r v).Nonempty :=
  Set.nonempty_of_mem (x := v) (by simp [ball])
@[simp] theorem ball_ne_empty (v : V) (r : Nat) : (ball G r v) ≠ ∅ :=
  Set.Nonempty.ne_empty (by simp)

@[simp] theorem ball_ncard_ne_zero [G.LocallyFinite] (v : V) (r : Nat) : (ball G r v).ncard ≠ 0 :=
  Set.ncard_ne_zero_of_mem (a := v) (by simp [ball])
@[simp] theorem ball_ncard_positive [G.LocallyFinite] (v : V) (r : Nat) : 0 < (ball G r v).ncard :=
  Nat.pos_of_ne_zero (by simp)

def slow_growth_at [G.LocallyFinite] (v : V) (e₁ : Nat := 1) (e₂ : Nat := 0) := Filter.Tendsto
  (fun r ↦ ((ball G (r + e₁) v).ncard : Real) / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 1)

theorem slow_growth_at_ext [G.LocallyFinite] (v : V) (e₁ e₂ e₃ e₄ : Nat) :
  e₁ ≠ e₂ → e₃ ≠ e₄ → (slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v e₃ e₄) := by
  let rec helper : ∀ e₁ e₂, e₂ < e₁ → (slow_growth_at G v e₁ e₂ ↔ slow_growth_at G v)
  | 0, _, _ => by contradiction
  | e₁ + 1, e₂ + 1, _ => by
    simp_rw [←helper e₁ e₂ (by omega), slow_growth_at, add_comm e₁, add_comm e₂, ←add_assoc]
    nth_rw 2 [←Filter.tendsto_add_atTop_iff_nat 1]
  | e₁ + 1, 0, _ => by
    cases Decidable.em (e₁ = 0) with | inl h => simp [h] | inr _ =>
    rw [←helper e₁ 0 (by omega)]; unfold slow_growth_at; constructor <;> intro h
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun r ↦ 1) (by simp) h <;>
      rw [Pi.le_def] <;> intro r
      · rw [one_le_div (by simp)]; simp [Set.ncard_le_ncard]
      · rw [div_le_div_iff_of_pos_right (by simp)]; simp [←add_assoc, Set.ncard_le_ncard]
    · conv =>
        arg 1; ext r; rw [←div_mul_div_cancel₀ (b := ↑(ball G (r + 1) v).ncard) (by simp)]
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
  intro h₁ h₂; rw [assistant e₁ e₂ h₁, assistant e₃ e₄ h₂]

theorem slow_growth_reach [G.LocallyFinite] (u v : V) :
  G.Reachable v u → slow_growth_at G v → slow_growth_at G u := by
  have helper (v u : V) (r₁ r₂ : Nat) (Avu : G.Adj v u) :
    ((ball G r₁ v).ncard : Real) / ((ball G (r₂ + 1) v).ncard : Real) ≤
    ((ball G (r₁ + 1) u).ncard : Real) / ((ball G r₂ u).ncard : Real) := by
    apply div_le_div₀ (by simp) _ (by simp) <;> norm_cast <;> apply Set.ncard_le_ncard _ (by simp)
    <;> rw [ball_eq_union_ball _ _ _] <;> exact Set.subset_biUnion_of_mem (by simp [Avu, Avu.symm])
  intro ⟨W_vu⟩; induction W_vu with | nil => tauto | @cons v w u A_vw W_wu ih =>
  intro h₃; apply ih; clear ih
  rw [slow_growth_at_ext G v 1 0 3 2 (by decide) (by decide)] at h₃
  have h₅ := (slow_growth_at_ext G v 3 2 5 0 (by decide) (by decide)).mp h₃
  rw [slow_growth_at_ext G w 1 0 4 1 (by decide) (by decide)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h₃ h₅ <;>
  rw [Pi.le_def] <;> intro _ <;> simp [helper, A_vw, A_vw.symm]

theorem slow_growth_all [G.LocallyFinite] (c : G.Preconnected) (v : V) :
  slow_growth_at G v → ∀ u, slow_growth_at G u := fun h _ ↦ slow_growth_reach _ _ _ (c _ _) h

def slow_boundary_at [G.LocallyFinite] (v : V) (e₁ e₂ : Nat := 0) := Filter.Tendsto
  (fun r ↦ ((sphere G (r + e₁) v).ncard : Real)  / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 0)

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
        rw [Nat.cast_sub (by simp [Set.ncard_le_ncard]), sub_div, add_assoc]
      rw [←sub_self 1]; apply Filter.Tendsto.sub h; rw [←slow_growth_at] at ⊢ h
      cases e₁ with | zero => simp [slow_growth_at] | succ e₁ =>
      rw [slow_growth_at_ext G v (e₁ + 1) 0 (e₁ + 1 + 1) 0 (by omega) (by omega)]
      exact h
    · conv =>
        arg 1; ext r;
        rw [←add_assoc, ball_eq_ball_sphere, Set.ncard_union_eq (by simp), Nat.cast_add, add_div]
      conv => arg 3; rw [←add_zero 1]
      apply Filter.Tendsto.add _ h; rw [←slow_growth_at]
      cases e₁ with | zero => simp [slow_growth_at] | succ e₁ =>
      rw [slow_growth_at_iff_slow_boundary_at v (e₁ + 1) 0 (by omega)]
      have t := tendsto_of_tendsto_of_tendsto_of_le_of_le (β := Nat) (α := Real)
        (g := fun r ↦ 0) (by simp) h (by simp [Pi.le_def])
        (f := fun r ↦ ↑(sphere G (r + e₁ + 1 + 1) v).ncard / ↑(ball G (r + 1) v).ncard)
        (by simp [Pi.le_def, ←add_assoc, div_le_div_of_nonneg_left, Set.ncard_le_ncard])
      simp_rw [show ∀ r : Nat, r + e₁ + 1 + 1 = r + 1 + e₁ + 1 by intro; ring] at t
      rw [Filter.tendsto_add_atTop_iff_nat 1 (α := Real)
        (f := fun r ↦ ↑(sphere G (r + e₁ + 1) v).ncard / ↑(ball G r v).ncard)] at t
      exact t

#check div_le_div_of_nonneg_left

#check Filter.tendsto_add_atTop_iff_nat
#check tendsto_of_tendsto_of_tendsto_of_le_of_le
theorem slow_boundary_at_ext [G.LocallyFinite] (v : V) (e₁ e₂ e₃ e₄ : Nat) :
  slow_boundary_at G v e₁ e₂ ↔ slow_boundary_at G v e₃ e₄ := by
  let rec helper : ∀ e₁ e₂, slow_boundary_at G v e₁ e₂ ↔ slow_boundary_at G v
    | 0, 0 => by tauto
    | e₁ + 1, e₂ + 1 => by
      simp_rw [←helper e₁ e₂, slow_boundary_at, add_comm e₁, add_comm e₂, ←add_assoc]
      nth_rw 2 [←Filter.tendsto_add_atTop_iff_nat 1]
    | e₁ + 1, 0 => by
      rw [←helper e₁ 0]; unfold slow_boundary_at; constructor <;> intro h
      · sorry
      · sorry
    | 0, e₂ + 1 => by
      rw [←helper 0 e₂]; unfold slow_boundary_at; constructor <;> intro h
      · sorry
      · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
          (g := fun r ↦ 0) (by simp) h (by simp [Pi.le_def])
        rw [Pi.le_def]; intro r; apply ENNReal.div_le_div_left;
        norm_cast; simp [←add_assoc, Set.encard_le_encard]


      -- exact
    -- intro e; induction e with | zero => simp | succ e ih =>
    -- rw [ih]; clear ih; unfold slow_boundary_at; constructor <;> intro h
    -- · have t := tendsto_of_tendsto_of_tendsto_of_le_of_le (β := Nat) (α := ENNReal)
    --     (g := fun r ↦ 0) (f := fun r ↦ ↑(sphere G (r + e) v).encard / ↑(ball G (r + 1) v).encard)
    --     (a := 0) (b := Filter.atTop) (by simp) h (by simp [Pi.le_def]) (by
    --       rw [Pi.le_def]; intro r; apply ENNReal.div_le_div_left;
    --       norm_cast; simp [Set.encard_le_encard])

    --   sorry
    -- · sorry



def udensity_at (S : Set V) (v : V) (d : ENNReal) (e : Nat := 0) :=
  Filter.limsup (β := Nat) (α := ENNReal)
  (fun r ↦ ((ball G (r + e) v) ∩ S).encard / (ball G r v).encard) Filter.atTop = d

theorem udensity_at_ext (S : Set V) (v : V) (d : ENNReal) (e : Nat) (s : slow_growth_at G v) :
  udensity_at G S v d ↔ udensity_at G S v d e := by
  induction e with
  | zero => tauto
  | succ e ih =>
    unfold udensity_at at ⊢ ih; unfold slow_growth_at at s; constructor <;> intro h
    · simp_rw [←add_assoc, ball_eq_ball_sphere, Set.union_inter_distrib_right]
      conv =>
        lhs; arg 1; ext r
        rw [Set.encard_union_eq (by simp), ENat.toENNReal_add, ENNReal.add_div]
      rw [←add_zero d, ←Pi.add_def, ENNReal.limsup_add_of_right_tendsto_zero]
      · rw [add_zero]; exact ih.mp h
      · sorry
    · apply ih.mpr
      sorry

theorem udensity_reach [G.LocallyFinite] (S : Set V) (u v : V) (d : ENNReal) :
  G.Reachable v u → udensity_at G S v d → udensity_at G S u d := by
  sorry

theorem udensity_all [G.LocallyFinite] (c : G.Preconnected) (S : Set V) (v : V) (d : ENNReal) :
  udensity_at G S v d → ∀ u, udensity_at G S u d :=
  fun h _ ↦ udensity_reach _ _ _ _ _ (c _ _) h
