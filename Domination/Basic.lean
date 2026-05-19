import Mathlib.Combinatorics.SimpleGraph.Basic

notation "N(" G ", " v ")" => SimpleGraph.neighborSet G v
notation "N[" G ", " v "]" => insert v N(G, v)
notation A "∆" B => symmDiff A B

universe u
variable {V : Type u} (G : SimpleGraph V)

----------------------------------------------------------------------------------------------------

def at_least (k : Nat) (S : Set V) := match k with
  | 0 => True
  | k' + 1 => ∃ (x : V), S x ∧ at_least k' (S \ {x})

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

def open_dom (k : Nat) (S : Set V) (v : V) := at_least k (N(G, v) ∩ S)
def closed_dom (k : Nat) (S : Set V) (v : V) := at_least k (N[G, v] ∩ S)

def open_doms (k : Nat) (S : Set V) := ∀ v, open_dom G k S v
def closed_doms (k : Nat) (S : Set V) := ∀ v, closed_dom G k S v

----------------------------------------------------------------------------------------------------

def open_dist (k : Nat) (S : Set V) (u v : V) := at_least k ((N(G, u) ∆ N(G, v)) ∩ S)
def closed_dist (k : Nat) (S : Set V) (u v : V) := at_least k ((N[G, u] ∆ N[G, v]) ∩ S)
def self_dist (k : Nat) (S : Set V) (u v : V) := at_least k (((N(G, u) ∆ N(G, v)) ∪ {u, v}) ∩ S)

def open_dists (k : Nat) (S : Set V) := ∀ u v, u ≠ v → open_dist G k S u v
def closed_dists (k : Nat) (S : Set V) := ∀ u v, u ≠ v → closed_dist G k S u v
def self_dists (k : Nat) (S : Set V) := ∀ u v, u ≠ v → self_dist G k S u v

----------------------------------------------------------------------------------------------------

def sharp_open_dist (k : Nat) (S : Set V) (u v : V) :=
  at_least k ((N(G, u) \ N(G, v)) ∩ S) ∨ at_least k ((N(G, v) \ N(G, u)) ∩ S)
def sharp_closed_dist (k : Nat) (S : Set V) (u v : V) :=
  at_least k ((N[G, u] \ N[G, v]) ∩ S) ∨ at_least k ((N[G, v] \ N[G, u]) ∩ S)

def sharp_open_dists (k : Nat) (S : Set V) := ∀ u v, u ≠ v → sharp_open_dist G k S u v
def sharp_closed_dists (k : Nat) (S : Set V) := ∀ u v, u ≠ v → sharp_closed_dist G k S u v

----------------------------------------------------------------------------------------------------

def odom (S : Set V) := open_doms G 1 S
def old (S : Set V) := open_doms G 1 S ∧ open_dists G 1 S
def redold (S : Set V) := open_doms G 2 S ∧ open_dists G 2 S
def detold (S : Set V) := open_doms G 2 S ∧ sharp_open_dists G 2 S
def errold (S : Set V) := open_doms G 3 S ∧ open_dists G 3 S
