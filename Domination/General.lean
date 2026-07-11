import Mathlib

theorem disjoint_inter_inter_of_disjoint_left
  {a b c d : Set α} (h : Disjoint a c := by assumption) : Disjoint (a ∩ b) (c ∩ d) := by
  intro; simp only [Set.le_eq_subset, Set.subset_inter_iff, Set.bot_eq_empty, Set.subset_empty_iff]
  rw [Set.eq_empty_iff_forall_notMem]; intro ⟨a, _⟩ ⟨b, _⟩ _ c
  exact (Set.disjoint_iff_forall_ne.mp h) (a c) (b c) rfl

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

theorem sum_biUnion_le [DecidableEq β] {s : Finset α} {g : α → Finset β} {f : β → Real}
  (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s.biUnion g, f x ≤ ∑ t ∈ s, ∑ x ∈ g t, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t s ht ih =>
    simp only [Finset.biUnion_insert, not_false_eq_true, Finset.sum_insert, ht]
    apply le_trans _ (add_le_add_right ih _)
    rw [←Finset.sum_union_inter]; apply le_add_of_nonneg_right; apply Finset.sum_nonneg; simp_all

theorem sum_biUnion_ge [DecidableEq β] {s : Finset α} {g : α → Finset β} {f : β → Real}
  (hf : ∀ x, 0 ≤ f x) (hg : ∀ t, {x ∈ s | t ∈ g x}.card ≤ k)
  : ∑ t ∈ s, ∑ x ∈ g t, f x ≤ k * ∑ x ∈ s.biUnion g, f x := by
  classical
  rw [Finset.mul_sum, Finset.sum_sigma']
  suffices h : ∑ x ∈ s.sigma g, f x.snd = ∑ i ∈ s.biUnion g, {x ∈ s | i ∈ g x}.card * f i by
    rw [h]; apply Finset.sum_le_sum; intros; apply mul_le_mul_of_nonneg_right _ (hf _); simp_all
  rw [←Finset.sum_fiberwise_of_maps_to' (show ∀ x ∈ s.sigma g, x.snd ∈ s.biUnion g by
    intro ⟨a, b⟩ h; simp only [Finset.mem_sigma, Finset.mem_biUnion] at *; exists a)]
  apply Finset.sum_congr rfl; intro v hv; rw [Finset.sum_const, nsmul_eq_mul]
  rw [show {i ∈ s.sigma g | i.snd = v} = {x ∈ s | v ∈ g x}.image (⟨·, v⟩) by
    clear hg hv hf f; ext ⟨t, y⟩; aesop]
  rw [Finset.card_image_of_injective _ (fun _ _ h ↦ by simp_all)]
