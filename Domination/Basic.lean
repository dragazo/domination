import Mathlib
import Domination.General

----------------------------------------------------------------------------------------------------

structure Policy (V : Type*) where
  f : V → Real
  m : Real := 1
  hm : 0 < m := by norm_num
  f₀ : ∀ r, 0 ≤ f r := by aesop
  fₘ : ∀ r, f r ≤ m := by aesop

structure Covering (G : SimpleGraph V) where
  t : Type*
  f : V → Set t
  d : Nat
  d₀ : d ≠ 0 := by norm_num
  h₁ : ∀ v, (f v).Nonempty := by aesop
  h₂ : ∀ v, (f v).Finite := by aesop
  h₃ : ∀ t, {v | t ∈ f v}.Finite := by aesop
  h₄ : ∀ u v, (f v ∩ f u).Nonempty → G.edist u v ≤ d := by aesop

def Tiling (G : SimpleGraph V) := { κ : Covering G // ∀ t v, t ∈ κ.f v ↔ κ.f v = {t} }

variable {V : Type*} {G : SimpleGraph V} {π : Policy V} {S : Set V}
variable {κ κ₁ κ₂ : Covering G} {τ τ₁ τ₂ : Tiling G}

def ball (G : SimpleGraph V) (r : Nat) (v : V) : Set V := { u | G.edist u v ≤ r }
def shell (G : SimpleGraph V) (r : Nat) (v : V) : Set V := { u | G.edist u v = r }

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

noncomputable instance Covering.fintype {t : κ.t} : Fintype {v | t ∈ κ.f v} := by
  apply Set.Finite.fintype; apply κ.h₃

def Covering.id (G : SimpleGraph V) : Covering G := { t := V, f := fun v ↦ {v}, d := 1 }

def Covering.closure (κ : Covering G) (S : Set V) : Set V :=
  ⋃ y ∈ S, ⋃ t ∈ κ.f y, {x | t ∈ κ.f x}

@[simp] theorem Covering.id_closure : (Covering.id G).closure S = S := by
  ext x; constructor <;> simp only [closure, id, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  · intro ⟨a, b, c, d, e⟩; rw [←e, d]; exact b
  · intro h; exact ⟨x, h, x, rfl, rfl⟩

theorem Covering.subset_closure : S ⊆ κ.closure S := by
  intro x h; simp only [closure, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  refine ⟨x, h, ?_⟩; simp only [and_self]; apply κ.h₁

theorem Covering.closure_subset : κ.closure S ⊆ ⋃ x ∈ S, ball G κ.d x := by
  intro x; simp only [closure, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, ball, and_imp,
    forall_exists_index]; intro a b c d e; refine ⟨a, b, ?_⟩; apply κ.h₄; exists c

theorem Covering.closure_mono (h : S₁ ⊆ S₂) : κ.closure S₁ ⊆ κ.closure S₂ := by
  intro x; simp only [closure, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, forall_exists_index,
    and_imp]; intro a b c d e; refine ⟨a, h b, c, d, e⟩

theorem Covering.closure_mem (h : x ∈ S) : x ∈ κ.closure S := by
  simp only [closure, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]; refine ⟨x, h, ?_⟩
  simp only [and_self]; apply κ.h₁

theorem Covering.closure_nonempty (h : S.Nonempty) : (κ.closure S).Nonempty := by
  apply Set.Nonempty.mono (s := S) κ.subset_closure h

theorem Covering.biUnion_closure_eq {f : V → Set V}
  : ⋃ x ∈ S, κ.closure (f x) = κ.closure (⋃ x ∈ S, f x) := by simp [Covering.closure]

noncomputable instance Covering.tiles_fintype [Fintype S] : Fintype (⋃ y ∈ S, κ.f y) := by
  apply Set.Finite.fintype; apply Set.Finite.biUnion (Set.toFinite _) (fun _ _ ↦ κ.h₂ _)

noncomputable instance Covering.closure_fintype [Fintype S] : Fintype (κ.closure S) := by
  apply Set.Finite.fintype; apply Set.Finite.biUnion (Set.toFinite _); intro _ _
  apply Set.Finite.biUnion (κ.h₂ _) (fun _ _ ↦ κ.h₃ _)

theorem Covering.closure_sum_le_tile_sum [Fintype S] {f : V → Real} (hf : ∀ v, 0 ≤ f v)
  : ∑ x ∈ (κ.closure S), f x
  ≤ ∑ t ∈ (⋃ y ∈ S, κ.f y).toFinset, ∑ x ∈ {v | t ∈ κ.f v}.toFinset, f x := by
  classical
  simp_rw [show κ.closure S =
    (⋃ y ∈ S, κ.f y).toFinset.biUnion (fun t => {v | t ∈ κ.f v}.toFinset) by simp [closure]]
  simp only [Finset.coe_biUnion, Set.coe_toFinset, Set.mem_iUnion, exists_prop, Set.iUnion_exists,
    Set.biUnion_and', Finset.toFinset_coe]; exact sum_biUnion_le hf

----------------------------------------------------------------------------------------------------

def Tiling.id (G : SimpleGraph V) : Tiling G := ⟨Covering.id G, by unfold Covering.id; aesop⟩

@[simp] theorem Tiling.closure_idemp : τ.1.closure (τ.1.closure S) = τ.1.closure S := by
  ext x; constructor <;> simp only [τ.2, Covering.closure, Set.mem_iUnion, exists_prop,
    Set.iUnion_exists, Set.biUnion_and', Set.mem_setOf_eq, forall_exists_index, and_imp]
  · intro a b c d e f g h i; refine ⟨a, b, c, d, ?_⟩; rw [i, ←h]; exact f
  · intro a b c d e; exact ⟨a, b, c, d, x, e, c, e, e⟩

theorem Tiling.closure_sum_eq_tile_sum [Fintype S] {f : V → Real} : ∑ x ∈ (τ.1.closure S), f x
  = ∑ y ∈ (⋃₀ (τ.1.f '' S)).toFinset, ∑ x ∈ {v | y ∈ τ.1.f v}.toFinset, f x := by
  classical
  rw [←Finset.sum_biUnion]
  · apply Finset.sum_congr _ (by simp); ext x; constructor <;> intro h <;> simp only [
    Covering.closure, Set.sUnion_image, Set.mem_iUnion, τ.2, exists_prop, Set.iUnion_exists,
    Set.biUnion_and', Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_biUnion] at *
    · obtain ⟨a, b, c, d, e⟩ := h; exact ⟨c, ⟨a, b, d⟩, e⟩
    · obtain ⟨a, ⟨b, c, d⟩, e⟩ := h; exact ⟨b, c, a, d, e⟩
  · simp only [Set.sUnion_image, Set.coe_toFinset, τ.2]; intro a b c d e
    simp only [Set.mem_iUnion, τ.2, exists_prop, ne_eq, Set.disjoint_toFinset] at *
    obtain ⟨b₁, b₂, b₃⟩ := b; obtain ⟨d₁, d₂, d₃⟩ := d; rw [Set.disjoint_left]; intro x hx hy
    simp only [Set.mem_setOf_eq] at hx hy; rw [hx] at hy; rw [Set.singleton_eq_singleton_iff] at hy
    contradiction

----------------------------------------------------------------------------------------------------

def Covering.cball (κ : Covering G) (r : Nat) (v : V) := κ.closure (ball G r v)

theorem cball_eq_union_cball : κ.cball (r + 1) v = ⋃ u ∈ ball G 1 v, κ.cball r u := by
  unfold Covering.cball; rw [κ.biUnion_closure_eq, ball_eq_union_ball]

theorem cball_nonempty : (κ.cball r v).Nonempty := κ.closure_nonempty ball_nonempty

theorem cball_mono (h : r₁ ≤ r₂)
  : κ.cball r₁ v ⊆ κ.cball r₂ v := κ.closure_mono (ball_mono h)

theorem cball_lower : ball G r v ⊆ κ.cball r v := κ.subset_closure

theorem cball_upper : κ.cball r v ⊆ ball G (r + κ.d) v := by
  apply subset_trans κ.closure_subset; simp only [ball, Set.mem_setOf_eq, Nat.cast_add,
    Set.iUnion_subset_iff, Set.setOf_subset_setOf]; intro a b c d
  apply le_trans (b := G.edist c a + G.edist a v) G.edist_triangle
  rw [add_comm]; exact add_le_add b d

noncomputable instance cball_fintype [G.LocallyFinite] : Fintype (κ.cball r v) := κ.closure_fintype

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

def slow_covering_at (κ : Covering G) (v : V) (e₁ := 1) (e₂ := 0) := Filter.Tendsto
  (fun r ↦ ((κ.cball (r + e₁) v).ncard : Real) / ((κ.cball (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 1)

def slow_boundary_at (G : SimpleGraph V) (v : V) (e₁ e₂ : Nat := 0) := Filter.Tendsto
  (fun r ↦ ((shell G (r + e₁) v).ncard : Real) / ((ball G (r + e₂) v).ncard : Real))
  Filter.atTop (nhds 0)

----------------------------------------------------------------------------------------------------

theorem slow_covering_at_ext [G.LocallyFinite]
  (e₃ := 1) (e₄ := 0) (h₁₂ : e₁ ≠ e₂ := by omega) (h₃₄ : e₃ ≠ e₄ := by omega)
  : slow_covering_at κ v e₁ e₂ ↔ slow_covering_at κ v e₃ e₄ := by
  let rec helper : ∀ e₁ e₂, e₂ < e₁ → (slow_covering_at κ v e₁ e₂ ↔ slow_covering_at κ v)
  | 0, _, _ => by contradiction
  | e₁ + 1, e₂ + 1, _ => by
    simp_rw [←helper e₁ e₂ (by omega), slow_covering_at, add_comm e₁, add_comm e₂, ←add_assoc]
    nth_rw 2 [←Filter.tendsto_add_atTop_iff_nat 1]
  | e₁ + 1, 0, _ => by
    cases Decidable.em (e₁ = 0) with | inl t => simp [t] | inr =>
    rw [←helper e₁ 0 (by omega)]; unfold slow_covering_at; constructor <;> intro h
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun r ↦ 1) (by simp) h <;> ball!
    · conv =>
        arg 1; ext r; rw [←div_mul_div_cancel₀ (b := ↑(κ.cball (r + 1) v).ncard) (by ball!)]
      conv => arg 3; rw [show (1 : Real) = 1 * 1 by simp]
      apply Filter.Tendsto.mul
      · simp_rw [add_comm e₁, ←add_assoc]; rw [←Filter.tendsto_add_atTop_iff_nat 1] at h; exact h
      · rw [←slow_covering_at] at ⊢ h; rw [helper e₁ 0 (by omega)] at h; exact h
  have assistant : ∀ {e₁ e₂}, e₁ ≠ e₂ → (slow_covering_at κ v e₁ e₂ ↔ slow_covering_at κ v) := by
    have t : ∀ e₁ e₂, slow_covering_at κ v e₁ e₂ → slow_covering_at κ v e₂ e₁ := fun e₁ e₂ h ↦ by
      unfold slow_covering_at
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
  conv_lhs =>
    arg 1; ext r; repeat rw [←Covering.id_closure (G := G) (S := ball G _ v), ←Covering.cball]
  conv_rhs =>
    arg 1; ext r; repeat rw [←Covering.id_closure (G := G) (S := ball G _ v), ←Covering.cball]
  rw [←slow_covering_at, ←slow_covering_at]; exact slow_covering_at_ext _ _

theorem slow_covering_at_iff [G.LocallyFinite]
  : slow_covering_at κ v e₁ e₂ ↔ slow_growth_at G v e₁ e₂ := by
  cases Decidable.em (e₁ = e₂) with | inl h => ball! [h, slow_covering_at, slow_growth_at] | inr =>
  constructor <;> intro h
  · unfold slow_growth_at; rw [←Filter.tendsto_add_atTop_iff_nat κ.d]
    simp_rw [add_assoc, add_comm κ.d, ←add_assoc]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun r ↦ ((κ.cball (r + e₁) v).ncard : Real) / (κ.cball (r + e₂ + κ.d) v).ncard)
      (h := fun r ↦ ((κ.cball (r + e₁ + κ.d) v).ncard : Real) / (κ.cball (r + e₂) v).ncard)
    · simp_rw [add_assoc]; rw [←slow_covering_at]
      cases Decidable.em (e₁ = e₂ + κ.d) with | inl t => ball! [t, slow_covering_at] | inr =>
      rw [slow_covering_at_ext e₁ e₂]; exact h
    · simp_rw [add_assoc]; rw [←slow_covering_at]
      cases Decidable.em (e₁ + κ.d = e₂) with | inl t => ball! [t, slow_covering_at] | inr =>
      rw [slow_covering_at_ext e₁ e₂]; exact h
    all_goals rw [Pi.le_def]; intro r; apply div_le_div₀ <;> ball!
  · unfold slow_covering_at; apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun r ↦ ((ball G (r + e₁) v).ncard : Real) / (ball G (r + e₂ + κ.d) v).ncard)
      (h := fun r ↦ ((ball G (r + e₁ + κ.d) v).ncard : Real) / (ball G (r + e₂) v).ncard)
    · simp_rw [add_assoc]; rw [←slow_growth_at]
      cases Decidable.em (e₁ = e₂ + κ.d) with | inl t => ball! [t, slow_growth_at] | inr =>
      rw [slow_growth_at_ext e₁ e₂]; exact h
    · simp_rw [add_assoc]; rw [←slow_growth_at]
      cases Decidable.em (e₁ + κ.d = e₂) with | inl t => ball! [t, slow_growth_at] | inr =>
      rw [slow_growth_at_ext e₁ e₂]; exact h
    all_goals rw [Pi.le_def]; intro r; apply div_le_div₀ <;> ball!

theorem slow_covering_at_iff' [G.LocallyFinite]
  : slow_covering_at κ₁ v e₁ e₂ ↔ slow_covering_at κ₂ v e₁ e₂ := by
  rw [slow_covering_at_iff, ←slow_covering_at_iff (κ := κ₂)]

theorem slow_covering_at_reach [G.LocallyFinite]
  (r : G.Reachable v u := by assumption) (st : slow_covering_at κ v := by assumption)
  : slow_covering_at κ u := by
  have helper (v u : V) (r₁ r₂ : Nat) (Avu : G.Adj v u) :
    ((κ.cball r₁ v).ncard : Real) / ((κ.cball (r₂ + 1) v).ncard : Real) ≤
    ((κ.cball (r₁ + 1) u).ncard : Real) / ((κ.cball r₂ u).ncard : Real) := by
    apply div_le_div₀ (by simp) _ (by ball!) <;> norm_cast <;> apply Set.ncard_le_ncard _ (by ball!)
    <;> rw [cball_eq_union_cball] <;> exact Set.subset_biUnion_of_mem (by simp [Avu, Avu.symm])
  have ⟨Wvu⟩ := r; induction Wvu with | nil => assumption | @cons v w u vw wu ih =>
  apply ih ⟨wu⟩; rw [slow_covering_at_ext 4 1]; apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((slow_covering_at_ext 3 2).mp st) ((slow_covering_at_ext 5).mp st)
    <;> ball! [helper, vw, vw.symm]

theorem slow_growth_at_reach [G.LocallyFinite]
  (r : G.Reachable v u := by assumption) (sg : slow_growth_at G v := by assumption)
  : slow_growth_at G u := by
  rw [←slow_covering_at_iff (κ := Covering.id G)] at ⊢ sg; exact slow_covering_at_reach r

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

noncomputable def cfudensity_at (κ : Covering G) [G.LocallyFinite]
  (π : Policy V) (v : V) (e₁ e₂ : Nat := 0) := Filter.limsup
  (fun r ↦ (∑ x ∈ (κ.cball (r + e₁) v), π.f x) / ↑(κ.cball (r + e₂) v).ncard) Filter.atTop

noncomputable def udensity_at (G : SimpleGraph V) (S : Set V) (v : V) (e₁ e₂ := 0) := Filter.limsup
  (fun r ↦ (((ball G (r + e₁) v) ∩ S).ncard : Real) / ↑(ball G (r + e₂) v).ncard) Filter.atTop

----------------------------------------------------------------------------------------------------

theorem cball_div_eventually_le [G.LocallyFinite] (e₁ e₂ : Nat) (ε : Real := 1)
  (hε : 0 < ε := by omega) (st : slow_covering_at κ v := by assumption) : ∀ᶠ r in Filter.atTop,
  ((κ.cball (r + e₁) v).ncard : Real) / (κ.cball (r + e₂) v).ncard ≤ 1 + ε := by
  apply Filter.Tendsto.eventually_le_const (v := 1) (by simp [hε])
  cases Decidable.em (e₁ = e₂) with | inl h => ball! [h] | inr h =>
  rw [←slow_covering_at, slow_covering_at_ext]; assumption

theorem cball_fdiv_eventually_le [G.LocallyFinite] (ε : Real := 1)
  (hε : 0 < ε := by norm_num) (st : slow_covering_at κ v := by assumption) : ∀ᶠ r in Filter.atTop,
  (∑ x ∈ (κ.cball (r + e₁) v), π.f x) / (κ.cball (r + e₂) v).ncard ≤ π.m + ε := by
  apply Filter.Eventually.mono (cball_div_eventually_le e₁ e₂ (ε / π.m) (div_pos hε π.hm) (κ := κ))
  intro r q; apply le_trans (b := π.m * (↑(κ.cball (r + e₁) v).ncard / ↑(κ.cball (r + e₂) v).ncard))
  · rw [mul_div]; apply div_le_div_of_nonneg_right <;> ball!
  · conv_rhs => rw [←mul_one π.m, ←mul_div_cancel₀ ε (ne_of_lt π.hm).symm, ←mul_add]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt π.hm); exact q

----------------------------------------------------------------------------------------------------

theorem cfudensity_at_ext [G.LocallyFinite]
  (e₃ e₄ : Nat := 0) (st : slow_covering_at κ v := by assumption)
  : cfudensity_at κ π v e₁ e₂ = cfudensity_at κ π v e₃ e₄ := by
  rw [cfudensity_at, ←Filter.limsup_nat_add _ e₃]; conv_lhs =>
    arg 1; ext r; rw [add_assoc, add_assoc]
    rw [←div_mul_div_cancel₀ (b := ((κ.cball (r + (e₁ + e₄)) v).ncard : Real)) (by ball!), mul_comm]
  rw [←one_mul (cfudensity_at κ π v e₃ e₄)]
  apply limsup_mul_eq (m₁ := 2) (m₂ := π.m + 1) _ _ (by ball!) (by ball!) _ _
  · cases Decidable.em (e₁ + e₄ = e₃ + e₂) with | inl h => ball! [h, slow_covering_at] | inr h =>
    rw [←slow_covering_at, slow_covering_at_ext]; assumption
  · simp_rw [add_comm e₃, ←add_assoc]
    rw [Filter.limsup_nat_add (fun r ↦ (∑ x ∈ (κ.cball (r + e₃) v).toFinset, π.f x)
      / (κ.cball (r + e₄) v).ncard) e₁, ←cfudensity_at]
  · apply Filter.Tendsto.eventually_le_const (v := 1) (by simp)
    cases Decidable.em (e₁ + e₄ = e₃ + e₂) with | inl t => ball! [t] | inr t =>
    rw [←slow_covering_at, slow_covering_at_ext]; assumption
  · exact cball_fdiv_eventually_le

theorem fudensity_at_ext [G.LocallyFinite]
  (e₃ e₄ : Nat := 0) (sg : slow_growth_at G v := by assumption)
  : fudensity_at G π v e₁ e₂ = fudensity_at G π v e₃ e₄ := by
  rw [←slow_covering_at_iff (κ := Covering.id G)] at sg; unfold fudensity_at
  have cvt {r}
    : (ball G r v).toFinset = ((Covering.id G).cball r v).toFinset := by ball! [Covering.cball]
  conv_lhs =>
    arg 1; ext r; rw [cvt, ←Covering.id_closure (G := G) (S := (ball G _ v)), ←Covering.cball]
  conv_rhs =>
    arg 1; ext r; rw [cvt, ←Covering.id_closure (G := G) (S := (ball G _ v)), ←Covering.cball]
  rw [←cfudensity_at, ←cfudensity_at]; exact cfudensity_at_ext _ _

theorem cfudensity_at_eq [G.LocallyFinite] (st : slow_covering_at κ v := by assumption)
  : cfudensity_at κ π v e₁ e₂ = fudensity_at G π v e₁ e₂ := by
  have sg := (slow_covering_at_iff).mp st
  have st' := (slow_covering_at_iff (κ := Covering.id G)).mpr sg
  apply le_antisymm
  · rw [fudensity_at_ext (e₁ + κ.d) e₂]; apply Filter.limsup_le_limsup
    · apply Filter.Eventually.of_forall; intro r; dsimp; apply div_le_div₀ (by ball!) _ (by ball!) _
      · apply Finset.sum_le_sum_of_subset_of_nonneg <;> ball! [←add_assoc, π.f₀]
      · apply le_trans (b := ↑(κ.cball (r + e₂) v).ncard) <;> ball!
    · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; ball!
    · exists π.m + 1; rw [Filter.eventually_map]; dsimp
      have cvt {r}
        : (ball G r v).toFinset = ((Covering.id G).cball r v).toFinset := by ball! [Covering.cball]
      conv =>
        arg 1; ext r; rw [cvt, ←Covering.id_closure (G := G) (S := ball G _ v), ←Covering.cball]
      exact cball_fdiv_eventually_le 1 (by norm_num) (by assumption)
  · rw [fudensity_at_ext e₁ (e₂ + κ.d)]; apply Filter.limsup_le_limsup
    · apply Filter.Eventually.of_forall; intro; apply div_le_div₀ (by ball!) _ (by ball!) _
      · apply Finset.sum_le_sum_of_subset_of_nonneg <;> ball! [←add_assoc, π.f₀]
      · ball! [←add_assoc]
    · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; ball!
    · exists π.m + 1; rw [Filter.eventually_map]; exact cball_fdiv_eventually_le

theorem cfudensity_at_reach [G.LocallyFinite]
  (r : G.Reachable v u := by assumption) (st : slow_covering_at κ v := by assumption)
  : cfudensity_at κ π v e₁ e₂ = cfudensity_at κ π u e₁ e₂ := by
  obtain ⟨Wvu⟩ := r; induction Wvu with | nil => rfl | @cons v w u Avw Wwu ih =>
  have st' := slow_covering_at_reach (SimpleGraph.Adj.reachable Avw); rw [←ih st']
  suffices h : ∀ v w, slow_covering_at κ v → slow_covering_at κ w → G.Adj w v →
    cfudensity_at κ π v e₁ e₂ ≤ cfudensity_at κ π w e₁ e₂ by
    apply le_antisymm <;> (apply h <;> simp [*, Avw.symm])
  intro v w stv stw Avw; rw [cfudensity_at_ext e₁ (e₂ + 1)]
  apply le_trans (b := cfudensity_at κ π w (e₁ + 1) e₂) _ (by rw [cfudensity_at_ext e₁ e₂])
  apply Filter.limsup_le_limsup
  · apply Filter.Eventually.of_forall; intro; apply div_le_div₀ (by ball!) _ (by ball!) _
    · apply Finset.sum_le_sum_of_subset_of_nonneg _ (by ball! [π.f₀])
      rw [Set.subset_toFinset, Set.coe_toFinset, ←add_assoc, cball_eq_union_cball]
      apply Set.subset_biUnion_of_mem; ball! [Avw]
    · norm_cast; apply Set.ncard_le_ncard _ (by ball!); rw [←add_assoc, cball_eq_union_cball]
      apply Set.subset_biUnion_of_mem; ball! [Avw.symm]
  · apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; ball!
  · exists π.m + 1; rw [Filter.eventually_map]; apply cball_fdiv_eventually_le <;> simp [*]

theorem fudensity_at_reach [G.LocallyFinite]
  (r : G.Reachable v u := by assumption) (sg : slow_growth_at G v := by assumption)
  : fudensity_at G π v e₁ e₂ = fudensity_at G π u e₁ e₂ := by
  rw [←slow_covering_at_iff (κ := Covering.id G)] at sg; have sg' := slow_covering_at_reach r sg
  (repeat rw [←cfudensity_at_eq (κ := Covering.id G)]); rw [cfudensity_at_reach]

----------------------------------------------------------------------------------------------------

theorem cfudensity_at_tile_le [G.LocallyFinite]
  (h : ∀ t, ∑ x ∈ {v | t ∈ τ.1.f v}.toFinset, π.f x ≤ d * τ.1.n)
  : cfudensity_at τ.1 π v ≤ d := by
  apply Filter.limsup_le_of_le (by apply Filter.IsBoundedUnder.isCoboundedUnder_le; exists 0; ball!)
  apply Filter.Eventually.of_forall; intro r
  rw [div_le_iff₀ (by ball!)]
  rw [Set.ncard_eq_toFinset_card', Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
  unfold Covering.cball; rw [τ.closure_sum_eq_tile_sum, τ.closure_sum_eq_tile_sum]
  apply Finset.sum_le_sum; intro t ht
  rw [←Finset.mul_sum, ←Nat.cast_sum, ←Finset.card_eq_sum_ones, ←Set.ncard_eq_toFinset_card']
  rw [τ.1.h₃]; apply h

theorem cfudensity_at_tile_ge [G.LocallyFinite]
  (h : ∀ t, ∑ x ∈ {v | t ∈ τ.1.f v}.toFinset, π.f x ≥ d * τ.1.n)
  (st : slow_covering_at τ.1 v := by assumption)
  : cfudensity_at τ.1 π v ≥ d := by
  apply Filter.le_limsup_of_frequently_le _
     (by exists π.m + 1; rw [Filter.eventually_map]; exact cball_fdiv_eventually_le)
  apply Filter.Frequently.of_forall; intro r
  rw [le_div_iff₀ (by ball!)]
  rw [Set.ncard_eq_toFinset_card', Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
  unfold Covering.cball; rw [τ.closure_sum_eq_tile_sum, τ.closure_sum_eq_tile_sum]
  apply Finset.sum_le_sum; intro t ht
  rw [←Finset.mul_sum, ←Nat.cast_sum, ←Finset.card_eq_sum_ones, ←Set.ncard_eq_toFinset_card']
  rw [τ.1.h₃]; apply h

theorem cfudensity_at_tile_eq [G.LocallyFinite]
  (h : ∀ t, ∑ x ∈ {v | t ∈ τ.1.f v}.toFinset, π.f x = d * τ.1.n)
  (st : slow_covering_at τ.1 v := by assumption)
  : cfudensity_at τ.1 π v = d := by
  apply le_antisymm
  · apply cfudensity_at_tile_le; intro; apply le_of_eq; rw [h]
  · apply cfudensity_at_tile_ge _; intro; apply le_of_eq; rw [h]
