import Mathlib

/-! 通用计数末步：全槽匹配加一个余块，推出逐组截断容量下界。
这不假设选出的块覆盖；所有假设是可检查的匹配证书。
-/

theorem matching_capacity_bound
    {Slot Block Group : Type*} [Fintype Slot] [Fintype Block] [DecidableEq Group]
    (group : Block → Group) (support : Group → Finset Slot)
    (matchBlock : Slot → Block) (hinj : Function.Injective matchBlock)
    (hincident : ∀ slot, slot ∈ support (group (matchBlock slot)))
    (anchor : Block) (hanchor : ∀ slot, matchBlock slot ≠ anchor) :
    Fintype.card Slot + 1 ≤
      ∑ ν ∈ Finset.univ.image group,
        min ((Finset.univ.filter (fun i => group i = ν)).card) ((support ν).card + 1) := by
  classical
  let matched : Finset Block := Finset.univ.image matchBlock
  let selected : Finset Block := insert anchor matched
  have hnot : anchor ∉ matched := by
    intro h
    obtain ⟨slot, _, heq⟩ := Finset.mem_image.mp h
    exact hanchor slot heq
  have hcard : selected.card = Fintype.card Slot + 1 := by
    rw [show selected = insert anchor matched from rfl, Finset.card_insert_of_notMem hnot]
    rw [show matched = Finset.univ.image matchBlock from rfl,
      Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hmatched : ∀ ν,
      (matched.filter (fun i => group i = ν)).card ≤ (support ν).card := by
    intro ν
    have heq : matched.filter (fun i => group i = ν) =
        (Finset.univ.filter (fun slot => group (matchBlock slot) = ν)).image matchBlock := by
      ext i
      constructor
      · intro hi
        obtain ⟨him, hν⟩ := Finset.mem_filter.mp hi
        obtain ⟨slot, _, hsi⟩ := Finset.mem_image.mp him
        exact Finset.mem_image.mpr ⟨slot,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hsi] using hν⟩, hsi⟩
      · intro hi
        obtain ⟨slot, hs, hsi⟩ := Finset.mem_image.mp hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, hsi⟩,
          by simpa only [hsi] using (Finset.mem_filter.mp hs).2⟩
    rw [heq, Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro slot hslot
    have hν := (Finset.mem_filter.mp hslot).2
    simpa only [hν] using hincident slot
  have hselected : ∀ ν,
      (selected.filter (fun i => group i = ν)).card ≤ (support ν).card + 1 := by
    intro ν
    have hsub : selected.filter (fun i => group i = ν) ⊆
        insert anchor (matched.filter (fun i => group i = ν)) := by
      intro i hi
      obtain ⟨hi, hν⟩ := Finset.mem_filter.mp hi
      rcases Finset.mem_insert.mp hi with hia | him
      · exact Finset.mem_insert.mpr (Or.inl hia)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨him, hν⟩))
    calc (selected.filter (fun i => group i = ν)).card
        ≤ (insert anchor (matched.filter (fun i => group i = ν))).card :=
          Finset.card_le_card hsub
      _ ≤ (matched.filter (fun i => group i = ν)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (support ν).card + 1 := Nat.add_le_add_right (hmatched ν) 1
  calc Fintype.card Slot + 1 = selected.card := hcard.symm
    _ = ∑ ν ∈ Finset.univ.image group,
        (selected.filter (fun i => group i = ν)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun i _ =>
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    _ ≤ ∑ ν ∈ Finset.univ.image group,
        min ((Finset.univ.filter (fun i => group i = ν)).card) ((support ν).card + 1) := by
      apply Finset.sum_le_sum
      intro ν _
      apply le_min
      · exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      · exact hselected ν

#print axioms matching_capacity_bound
