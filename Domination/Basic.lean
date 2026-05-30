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

def ball (r : Nat) (v : V) : Set V := { u | G.edist u v ≤ r }

theorem ball_succ (v : V) (r : Nat) : (ball G (r + 1) v) = ⋃ u ∈ N[G, v], ball G r u := by
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

@[simp] theorem ball_subset (v : V) (r e : Nat) : ball G r v ⊆ ball G (r + e) v := by
  induction e with
  | zero => simp
  | succ e ih => apply subset_trans ih; simp [←add_assoc, ball_succ]

@[simp] theorem ball_finite [G.LocallyFinite] (v : V) (r : Nat) : Set.Finite (ball G r v) := by
  induction r generalizing v with
  | zero => simp [ball]
  | succ r ih => rw [ball_succ]; exact
    Set.Finite.biUnion (Set.finite_insert.mpr (Set.toFinite _)) (fun i h ↦ ih i)

@[simp] theorem ball_nonempty (v : V) (r : Nat) : ball G r v ≠ ∅ := by
  intro h; rw [Set.eq_empty_iff_forall_notMem] at h; apply h v; simp [ball]

@[simp] theorem ball_encard_div_self [G.LocallyFinite] (v : V) (r : Nat) :
  (ball G r v).encard / (ball G r v).encard = (1 : ENNReal) :=
  ENNReal.div_self (by norm_cast; simp) (by simp)
@[simp] theorem ball_encard_mul_inv_self [G.LocallyFinite] (v : V) (r : Nat) :
  (ball G r v).encard * (↑(ball G r v).encard)⁻¹ = (1 : ENNReal) := by
  simp [←div_eq_mul_inv]

def slow_growth_at (v : V) (e : Nat := 1) := Filter.Tendsto (β := ENNReal)
  (fun r ↦ (ball G (r + e) v).encard  / (ball G r v).encard)
  Filter.atTop (nhds 1)

theorem slow_growth_at_ext_succ [G.LocallyFinite] (v : V) (e : Nat) :
  slow_growth_at G v ↔ slow_growth_at G v (e + 1) := by
  simp_rw [slow_growth_at, div_eq_mul_inv]
  induction e with
  | zero => simp
  | succ e ih =>
    constructor <;> intro h
    · conv =>
        arg 1; ext r
        rw [←mul_one ((ball G r v).encard : ENNReal)⁻¹, ←ball_encard_mul_inv_self G v (r + (e + 1))]
        rw [show ∀ a b c, a * (b⁻¹ * (c * c⁻¹)) = (a * c⁻¹) * (c * b⁻¹) by intros; ring]
      conv => arg 3; rw [←mul_one 1]
      apply ENNReal.Tendsto.mul (ha := by simp) (hb := by simp) (hmb := by exact ih.mp h)
        (ma := fun r ↦ (ball G (r + (e + 1 + 1)) v).encard * (↑(ball G (r + (e + 1)) v).encard)⁻¹)
        (mb := fun r ↦ (ball G (r + (e + 1)) v).encard * (↑(ball G r v).encard)⁻¹)
      simp_rw [show ∀ r, r + (e + 1 + 1) = (r + (e + 1)) + 1 by intro; ring]
      rw [Filter.tendsto_add_atTop_iff_nat (e + 1) (α := ENNReal)
        (f := fun r ↦ (ball G (r + 1) v).encard * (↑(ball G r v).encard)⁻¹)]
      exact h
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (α := ENNReal)
        (g := fun r ↦ 1) (hg := by simp) (hh := by exact h)
        (h := fun r ↦ (ball G (r + (e + 1 + 1)) v).encard * (↑(ball G r v).encard)⁻¹)
      · rw [Pi.le_def]; intro r
        rw [←ENNReal.mul_le_mul_iff_left (c := (ball G r v).encard) (by norm_cast; simp) (by simp)]
        conv => rhs; rw [mul_assoc]; rhs; simp [mul_comm]
        simp [Set.encard_le_encard]
      · rw [Pi.le_def]; intro r
        apply mul_le_mul _ (by simp) (by simp) (by simp)
        rw [show ∀ r e, r + (e + 1 + 1) = r + 1 + (e + 1) by intros; ring]
        simp [Set.encard_le_encard]
theorem slow_growth_at_ext [G.LocallyFinite] (v : V) (e : Nat) (he : e ≠ 0) :
  slow_growth_at G v ↔ slow_growth_at G v e := match e with
  | Nat.zero => by contradiction
  | Nat.succ e => slow_growth_at_ext_succ G v e

theorem slow_growth_reach [G.LocallyFinite] (u v : V) :
  G.Reachable v u → slow_growth_at G v → slow_growth_at G u := by
  have helper : ∀ v u r₁ r₂, G.Adj v u →
    ((ball G r₁ v).encard : ENNReal) * (↑(ball G (r₂ + 1) v).encard)⁻¹ ≤
    (ball G (r₁ + 1) u).encard * (↑(ball G r₂ u).encard)⁻¹ := by
    intro v u r₁ r₂ Avu; rw [←div_eq_mul_inv, ←div_eq_mul_inv]
    apply ENNReal.div_le_div <;> norm_cast <;> apply Set.encard_le_encard
    · rw [ball_succ G u r₁]; exact Set.subset_biUnion_of_mem (Or.inr Avu.symm)
    · rw [ball_succ G v r₂]; exact Set.subset_biUnion_of_mem (Or.inr Avu)
  intro ⟨W_vu⟩
  induction W_vu with
  | nil => tauto
  | @cons v w u A_vw W_wu ih =>
    intro h₃; apply ih
    have h₅ := (slow_growth_at_ext G v 5 (by decide)).mp h₃
    rw [slow_growth_at_ext G w 3 (by decide)]
    simp_rw [slow_growth_at, div_eq_mul_inv] at ⊢ h₃ h₅
    rw [←Filter.tendsto_add_atTop_iff_nat 2] at h₃
    rw [←Filter.tendsto_add_atTop_iff_nat 1]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (hg := by exact h₃) (hh := by exact h₅)
    · rw [Pi.le_def]; intro r; exact helper _ _ _ _ A_vw
    · rw [Pi.le_def]; intro r; exact helper _ _ _ _ A_vw.symm

theorem slow_growth [G.LocallyFinite] (c : G.Preconnected) (v : V) :
  slow_growth_at G v → ∀ u, slow_growth_at G u := fun h _ ↦ slow_growth_reach _ _ _ (c _ _) h

class SlowGrowth where
  conn : G.Connected
  slow : ∀ v, slow_growth_at G v

noncomputable def density_at (S : Set V) (v : V) :=
  Filter.limsup (fun r ↦ ((B(G, r, v) ∩ S).encard : ENNReal) / (B(G, r, v).encard : ENNReal))
