import Domination.Basic

theorem old_is_odom (S : Set V) : old G S → odom G S := And.left
theorem redold_is_old (S : Set V) : redold G S → old G S :=
  fun ⟨a, b⟩ ↦ ⟨
    fun v ↦ at_least_le (by decide) (a v),
    fun u v h ↦ at_least_le (by decide) (b u v h)⟩
theorem detold_is_redold (S : Set V) : detold G S → redold G S :=
  fun ⟨a, b⟩ ↦ ⟨
    fun v ↦ a v,
    fun u v h ↦ (b u v h).elim
      (fun q ↦ at_least_subset (Set.inter_subset_inter_left _ Set.subset_union_left) q)
      (fun q ↦ at_least_subset (Set.inter_subset_inter_left _ Set.subset_union_right) q)⟩
theorem errold_is_detold (S : Set V) : errold G S → detold G S :=
  fun ⟨a, b⟩ ↦ ⟨
    fun v ↦ at_least_le (by decide) (a v),
    fun u v h ↦ let g := b; at_least_union_ph _⟩
