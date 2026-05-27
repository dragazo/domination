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
  (fun _ ih _ _ ⟨x, p, h⟩ ↦ let ⟨k₁, k₂, a, b, c⟩ := ih _ _ (Set.union_diff_distrib ▸ h); p.elim
    (fun l ↦ ⟨k₁ + 1, k₂, by omega, ⟨x, l, b⟩, at_least_subset Set.diff_subset c⟩)
    (fun r ↦ ⟨k₁, k₂ + 1, by omega, at_least_subset Set.diff_subset b, ⟨x, r, c⟩⟩))
  S T

theorem at_least_union_ph {k : Nat} {S T : Set V} :
  at_least (2 * k + 1) (S ∪ T) → at_least (k + 1) S ∨ at_least (k + 1) T :=
  fun h ↦ let ⟨k₁, k₂, p, q, r⟩ := at_least_union h; (Nat.lt_or_ge k₁ (k + 1)).elim
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

def ball (r : Nat) (v : V) : Set V := { u | G.dist u v ≤ r }

theorem ball_zero (c : G.Preconnected) (v : V) : (ball G 0 v) = {v} := by
  ext x; constructor <;> rw [ball, Set.mem_setOf_eq, nonpos_iff_eq_zero] <;> intro h
  · match SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h with
    | Or.inl h => exact Set.mem_singleton_of_eq h
    | Or.inr h => exact False.elim (h (c x v))
  · rw [Set.eq_of_mem_singleton h]; exact SimpleGraph.dist_self

theorem reachable_of_dist_ne_zero (u v : V) (h : G.dist u v ≠ 0) : G.Reachable u v := by
  contrapose h; exact SimpleGraph.dist_eq_zero_of_not_reachable h

#check SimpleGraph.dist
theorem ball_succ (v : V) (r : Nat) : (ball G (r + 1) v) = ⋃ u ∈ N[G, v], ball G r u := by
  ext x; constructor <;> intro h
  · simp only [ball, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at *
    by_cases d : G.dist x v ≤ r
    · exact ⟨v, Set.mem_insert _ _, d⟩
    · let p : G.dist x v = r + 1 := by omega
      let ⟨w⟩ := reachable_of_dist_ne_zero G x v (by omega)
      sorry
  · simp [ball] at *
    match h with
    | Or.inl h => exact Nat.le_add_right_of_le h
    | Or.inr h => obtain ⟨z, z₁, z₂⟩ := h;

  -- · by_cases d : G.dist x v = 0
  --   · match SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp d with
  --     | Or.inl t => rw [t]; simp [ball]





theorem ball_finite [G.LocallyFinite] (c : G.Preconnected) (v : V) (r : Nat) : Set.Finite (ball G r v) := by
  induction r generalizing v with
  | zero => rw [ball_zero G c]; exact Set.finite_singleton v
  | succ r ih =>

  _

def slow_growth_at (v : V) := Filter.Tendsto
  (fun r ↦ ((ball G (r + 1) v).ncard : Real) / ((ball G r v).ncard : Real)) Filter.atTop (nhds 1)



theorem slow_growth_adj [G.LocallyFinite] (u v : V) : u ∈ N(G, v) → slow_growth_at G v → slow_growth_at G u := by
  intro adj h
  have g : ∀ r, |B(G, r + 1, v)| ≤ |B(G, r + 2, u)| :=
    fun r ↦ Set.ncard_le_ncard (fun w ↦ _) _





noncomputable def density_at (S : Set V) (v : V) :=
  Filter.limsup (fun r ↦ (|B(G, r, v) ∩ S| : Real) / (|B(G, r, v)| : Real))
