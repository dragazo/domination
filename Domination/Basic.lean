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

theorem ball_finite [G.LocallyFinite] (v : V) (r : Nat) : Set.Finite (ball G r v) := by
  induction r generalizing v with
  | zero => simp [ball]
  | succ r ih => rw [ball_succ]; exact
    Set.Finite.biUnion (Set.finite_insert.mpr (Set.toFinite N(G, v))) (fun i h ↦ ih i)

theorem ball_nonempty (v : V) (r : Nat) : Set.Nonempty (ball G r v) := ⟨v, by simp [ball]⟩

@[simp] theorem ball_encard_div_self [G.LocallyFinite] (v : V) (r : Nat) :
  (ball G r v).encard / (ball G r v).encard = (1 : ENNReal) := by
  apply ENNReal.div_self
  · norm_cast; exact Set.encard_ne_zero.mpr (ball_nonempty G v r)
  · norm_cast; exact Set.encard_ne_top_iff.mpr (ball_finite G v r)
@[simp] theorem ball_encard_mul_inv_self [G.LocallyFinite] (v : V) (r : Nat) :
  (ball G r v).encard * (↑(ball G r v).encard)⁻¹ = (1 : ENNReal) := by
  rw [←div_eq_mul_inv, ball_encard_div_self]

def slow_growth_at (v : V) (e : Nat := 1) := Filter.Tendsto (β := ENNReal)
  (fun r ↦ (ball G (r + e) v).encard  / (ball G r v).encard)
  Filter.atTop (nhds 1)

theorem slow_growth_at_ext [G.LocallyFinite] (v : V) :
  slow_growth_at G v → ∀ e, slow_growth_at G v e := by
  intro h e; induction e with
  | zero => simp [slow_growth_at]
  | succ e ih =>
    simp_rw [slow_growth_at, div_eq_mul_inv] at ⊢ ih h
    conv =>
      arg 1; ext r
      rw [←mul_one ((ball G r v).encard : ENNReal)⁻¹, ←ball_encard_mul_inv_self G v (r + e)]
      rw [show ∀ a b c, a * (b⁻¹ * (c * c⁻¹)) = (a * c⁻¹) * (c * b⁻¹) by intros; ring]
    conv => arg 3; rw [←mul_one 1]
    apply ENNReal.Tendsto.mul (ha := by simp) (hb := by simp) (hmb := by exact ih)
      (ma := fun r ↦ (ball G (r + (e + 1)) v).encard * (↑(ball G (r + e) v).encard)⁻¹)
      (mb := fun r ↦ (ball G (r + e) v).encard * (↑(ball G r v).encard)⁻¹)
    simp_rw [show ∀ r, r + (e + 1) = (r + e) + 1 by intro; ring]
    rw [Filter.tendsto_add_atTop_iff_nat e (α := ENNReal)
      (f := fun r ↦ (ball G (r + 1) v).encard * (↑(ball G r v).encard)⁻¹)]
    exact h

-- theorem slow_growth_at_ext [G.LocallyFinite] (v : V) (e : Nat) :
--   slow_growth_at G v ↔ slow_growth_at G v e := by
--   simp_rw [slow_growth_at, div_eq_mul_inv] <;> constructor <;> intro h
--   · induction e with
--   | zero => simp [slow_growth_at]
--   | succ e ih =>
--     conv =>
--       arg 1; ext r
--       rw [←mul_one ((ball G r v).encard : ENNReal)⁻¹, ←ball_encard_mul_inv_self G v (r + e)]
--       rw [show ∀ a b c, a * (b⁻¹ * (c * c⁻¹)) = (a * c⁻¹) * (c * b⁻¹) by intros; ring]
--     conv => arg 3; rw [←mul_one 1]
--     apply ENNReal.Tendsto.mul (ha := by simp) (hb := by simp) (hmb := by exact ih)
--       (ma := fun r ↦ (ball G (r + (e + 1)) v).encard * (↑(ball G (r + e) v).encard)⁻¹)
--       (mb := fun r ↦ (ball G (r + e) v).encard * (↑(ball G r v).encard)⁻¹)
--     simp_rw [show ∀ r, r + (e + 1) = (r + e) + 1 by intro; ring]
--     rw [Filter.tendsto_add_atTop_iff_nat e (α := ENNReal)
--       (f := fun r ↦ (ball G (r + 1) v).encard * (↑(ball G r v).encard)⁻¹)]
--     exact h
--   ·

-- #check Filter.Tendsto.inv
-- #check mul_inv_rev
-- #check ENNReal.mul_inv
-- #check inv_one
-- theorem slow_growth_at_ext [G.LocallyFinite] (v : V) (e : Nat) :
--   slow_growth_at G v ↔ slow_growth_at G v (e + 1) := by
--   simp_rw [slow_growth_at, div_eq_mul_inv]
--   induction e with
--   | zero => simp
--   | succ e ih =>
--     constructor <;> intro h
--     · conv =>
--         arg 1; ext r
--         rw [←mul_one ((ball G r v).encard : ENNReal)⁻¹, ←ball_encard_mul_inv_self G v (r + (e + 1))]
--         rw [show ∀ a b c, a * (b⁻¹ * (c * c⁻¹)) = (a * c⁻¹) * (c * b⁻¹) by intros; ring]
--       conv => arg 3; rw [←mul_one 1]
--       apply ENNReal.Tendsto.mul (ha := by simp) (hb := by simp) (hmb := by exact ih.mp h)
--         (ma := fun r ↦ (ball G (r + (e + 1 + 1)) v).encard * (↑(ball G (r + (e + 1)) v).encard)⁻¹)
--         (mb := fun r ↦ (ball G (r + (e + 1)) v).encard * (↑(ball G r v).encard)⁻¹)
--       simp_rw [show ∀ r, r + (e + 1 + 1) = (r + (e + 1)) + 1 by intro; ring]
--       rw [Filter.tendsto_add_atTop_iff_nat (e + 1) (α := ENNReal)
--         (f := fun r ↦ (ball G (r+ 1) v).encard * (↑(ball G r v).encard)⁻¹)]
--       exact h
--     · conv =>
--         arg 1; ext r
--         rw [←mul_one ((ball G r v).encard : ENNReal)⁻¹, ←ball_encard_mul_inv_self G v (r + (e + 1 + 1))]
--         rw [show ∀ a b c, a * (b⁻¹ * (c * c⁻¹)) = (a * c⁻¹) * (c * b⁻¹) by intros; ring]
--       conv => arg 3; rw [←mul_one 1]
--       apply ENNReal.Tendsto.mul (ha := by simp) (hb := by simp) (hmb := by exact h)
--         (ma := fun r ↦ (ball G (r + 1) v).encard * (↑(ball G (r + (e + 1 + 1)) v).encard)⁻¹)
--         (mb := fun r ↦ (ball G (r + (e + 1 + 1)) v).encard * (↑(ball G r v).encard)⁻¹)
--       simp_rw [show ∀ r, r + (e + 1 + 1) = (r + 1) + (e + 1) by intro; ring]
--       rw [Filter.tendsto_add_atTop_iff_nat 1 (α := ENNReal)
--         (f := fun r ↦ (ball G r v).encard * (↑(ball G (r + (e + 1)) v).encard)⁻¹)]
--       conv =>
--         arg 1; ext r;
--         rw [←inv_inv (G := ENNReal) (ball G r v).encard]
--         rw [←ENNReal.mul_inv
--           (by right; norm_cast; exact Set.encard_ne_top_iff.mpr (ball_finite G v (r + (e + 1))))
--           (by right; norm_cast; exact Set.encard_ne_zero.mpr (ball_nonempty G v (r + (e + 1))))]
--       conv => arg 3; rw [←inv_one]
--       apply Filter.Tendsto.inv
--       conv => arg 1; ext r; rw [mul_comm]


  -- · induction e with
  -- | zero => simp [slow_growth_at]
  -- | succ e ih =>
  --   conv =>
  --     arg 1; ext r
  --     rw [←mul_one ((ball G r v).encard : ENNReal)⁻¹, ←ball_encard_mul_inv_self G v (r + e)]
  --     rw [show ∀ a b c, a * (b⁻¹ * (c * c⁻¹)) = (a * c⁻¹) * (c * b⁻¹) by intros; ring]
  --   conv => arg 3; rw [←mul_one 1]
  --   apply ENNReal.Tendsto.mul (ha := by simp) (hb := by simp) (hmb := by exact ih)
  --     (ma := fun r ↦ (ball G (r + (e + 1)) v).encard * (↑(ball G (r + e) v).encard)⁻¹)
  --     (mb := fun r ↦ (ball G (r + e) v).encard * (↑(ball G r v).encard)⁻¹)
  --   simp_rw [show ∀ r, r + (e + 1) = (r + e) + 1 by intro; ring]
  --   rw [Filter.tendsto_add_atTop_iff_nat e (α := ENNReal)
  --     (f := fun r ↦ (ball G (r + 1) v).encard * (↑(ball G r v).encard)⁻¹)]
  --   exact h
  -- ·

-- theorem slow_growth_at_ext (a b c d : Nat)

#check tendsto_of_tendsto_of_tendsto_of_le_of_le
#check slow_growth_at_ext
theorem slow_growth_reach [G.LocallyFinite] (u v : V) :
  G.Reachable v u → slow_growth_at G v → slow_growth_at G u := by
  have helper : ∀ v u r, G.Adj v u →
    ((ball G (r + 2) v).encard : ENNReal) * (↑(ball G (r + 1) v).encard)⁻¹ ≤
    (ball G (r + 3) u).encard * (↑(ball G r u).encard)⁻¹ := by
    intro v u r Avu; rw [←div_eq_mul_inv, ←div_eq_mul_inv]
    apply ENNReal.div_le_div <;> norm_cast <;> apply Set.encard_le_encard
    · rw [ball_succ G u (r + 2)]; exact Set.subset_biUnion_of_mem (Or.inr Avu.symm)
    · rw [ball_succ G v r]; exact Set.subset_biUnion_of_mem (Or.inr Avu)
  intro ⟨W_vu⟩
  induction W_vu with
  | nil => tauto
  | @cons v w u A_vw W_wu ih => exact fun h₁ ↦ ih (by
      have h₅ := slow_growth_at_ext G v h₁ 5
      simp_rw [slow_growth_at, div_eq_mul_inv] at ⊢ h₁ h₅


      -- apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        -- (g := fun r ↦ (ball G


    )



theorem slow_growth [G.LocallyFinite] (c : G.Preconnected) (v : V) :
  slow_growth_at G v → ∀ u, slow_growth_at G u := fun h _ ↦ slow_growth_reach _ _ _ (c _ _) h

class SlowGrowth where
  conn : G.Connected
  slow : ∀ v, slow_growth_at G v

noncomputable def density_at (S : Set V) (v : V) :=
  Filter.limsup (fun r ↦ ((B(G, r, v) ∩ S).encard : ENNReal) / (B(G, r, v).encard : ENNReal))
