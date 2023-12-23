import data.set.image
import data.set.ncard
import data.set.function
import data.set.basic
import data.nat.lattice 
import order.minimal 
import data.finset.locally_finite
import data.nat.interval 


section minimal

variables {α : Type*} {r : α → α → Prop} {s : set α} {x y : α} {P : α → Prop}

lemma mem_maximals_iff' [is_antisymm α r] :
  x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r x y → x = y :=
begin
  simp only [maximals, set.mem_sep_iff, and.congr_right_iff],  
  refine λ hx, ⟨λ h y hys hxy, antisymm hxy (h hys hxy), λ h y hys hxy, _⟩, 
  convert hxy; rw h hys hxy, 
end 

lemma mem_minimals_iff' [is_antisymm α r] :
  x ∈ minimals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r y x → x = y :=
by { convert mem_maximals_iff', apply is_antisymm.swap }

lemma mem_maximals_prop_iff [is_antisymm α r] : 
  x ∈ maximals r P ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
mem_maximals_iff'

lemma mem_maximals_set_of_iff [is_antisymm α r] : 
  x ∈ maximals r (set_of P) ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
mem_maximals_iff'

lemma mem_minimals_prop_iff [is_antisymm α r] : 
  x ∈ minimals r P ↔ P x ∧ ∀ ⦃y⦄, P y → r y x → x = y :=
mem_minimals_iff'

lemma mem_minimals_set_of_iff [is_antisymm α r] : 
  x ∈ minimals r (set_of P) ↔ P x ∧ ∀ ⦃y⦄, P y → r y x → x = y :=
mem_minimals_iff'

end minimal

open set

section finite -- taken from mathlib.data.set.finite.lean

namespace set

variables {α β : Type*}

lemma finite.exists_maximal [finite α] [partial_order α] (P : α → Prop) (h : ∃ x, P x) :
  ∃ m, P m ∧ ∀ x, P x → m ≤ x → m = x :=
begin
  obtain ⟨m, hm,hm'⟩ := finite.exists_maximal_wrt (@id α) (set_of P) (to_finite _) h,
  exact ⟨m, hm, hm'⟩,
end

end set

end finite

section ncard -- taken from mathlib.data.set.ncard.lean

variables {α : Type*} {s t r : set α} {x y z : α}

namespace set

lemma enat.coe_inj {m n : ℕ} : (m : ℕ∞) = n ↔ m = n := 
nat.cast_inj

lemma enat.coe_le_coe_iff {m n : ℕ} : (m : ℕ∞) ≤ n ↔ m ≤ n :=
nat.cast_le  

/-- The cardinality of a set as a member of `enat`. -/
noncomputable def encard (s : set α) : ℕ∞ := part_enat.with_top_equiv (part_enat.card s)

lemma finite.encard_eq (hs : s.finite) : s.encard = (s.ncard : ℕ∞) := 
begin
  obtain ⟨s, rfl⟩ := hs.exists_finset_coe, 
  simp_rw [encard, part_enat.card_eq_coe_fintype_card,ncard_coe_finset,  
    part_enat.with_top_equiv_coe, nat.cast_inj, finset.coe_sort_coe, fintype.card_coe], 
end 

lemma infinite.encard_eq (hs : s.infinite) : s.encard = ⊤ := 
begin
  haveI := hs.to_subtype, 
  rw [encard, part_enat.card_eq_top_of_infinite, part_enat.with_top_equiv_top], 
end 

@[simp] lemma encard_to_nat_eq (s : set α) : s.encard.to_nat = s.ncard :=
begin
  obtain (h | h) := s.finite_or_infinite, 
  simp [h.encard_eq], 
  simp [h.ncard, h.encard_eq], 
end 

lemma encard_insert_of_not_mem (h : x ∉ s) : (insert x s).encard = s.encard + 1 :=
begin
  obtain (hs | hs) := s.finite_or_infinite, 
  { rw [hs.encard_eq, (hs.insert x).encard_eq, ncard_insert_of_not_mem h hs], simp },
  rw [hs.encard_eq, (hs.mono (subset_insert _ _)).encard_eq, with_top.top_add],  
end 

@[simp] lemma encard_eq_top_iff_infinite : s.encard = ⊤ ↔ s.infinite :=
begin
  refine ⟨λ h hfin, _, infinite.encard_eq⟩,
  rw hfin.encard_eq at h, 
  simpa only [with_top.nat_ne_top] using h, 
end 

@[simp] lemma encard_lt_top_iff_finite : s.encard < ⊤ ↔ s.finite :=
by rw [lt_top_iff_ne_top, ←not_infinite, ←encard_eq_top_iff_infinite]

lemma finite_of_encard_le_coe {k : ℕ} (h : s.encard ≤ k) : s.finite :=
encard_lt_top_iff_finite.mp (h.trans_lt (with_top.coe_lt_top k))

lemma encard_le_coe_iff {k : ℕ} : s.encard ≤ k ↔ s.finite ∧ s.ncard ≤ k :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have hs := finite_of_encard_le_coe h, 
    rw [hs.encard_eq, nat.cast_le] at h,
    exact ⟨hs, h⟩ },
  rw [h.1.encard_eq, nat.cast_le], 
  exact h.2, 
end 

lemma encard_union_eq (h : disjoint s t) : (s ∪ t).encard = s.encard + t.encard :=
begin
  obtain (hf | hi) := (s ∪ t).finite_or_infinite, 
  { obtain ⟨hs, ht⟩ := finite_union.mp hf,  
    rw [hf.encard_eq, hs.encard_eq, ht.encard_eq, ←nat.cast_add, nat.cast_inj, 
      ncard_union_eq h hs ht] },
  rw [hi.encard_eq],
  obtain (h | h) := infinite_union.mp hi; simp [h.encard_eq], 
end 

lemma encard_diff_add_encard_inter (s t : set α) : 
  (s \ t).encard + (s ∩ t).encard = s.encard :=
by rw [←encard_union_eq (disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left), 
    diff_union_inter]

lemma encard_eq_coe_iff {k : ℕ} : s.encard = k ↔ s.finite ∧ s.ncard = k :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have hs := finite_of_encard_le_coe h.le, 
    rw [hs.encard_eq, nat.cast_inj] at h,
    exact ⟨hs,h⟩},
  rw [h.1.encard_eq, h.2], 
end 

lemma encard_subset_le (hst : s ⊆ t) : s.encard ≤ t.encard := 
begin
  obtain (ht | ht) := t.finite_or_infinite, 
  { rw [ht.encard_eq, (ht.subset hst).encard_eq, nat.cast_le],
    exact ncard_le_of_subset hst ht },
  exact le_top.trans_eq ht.encard_eq.symm, 
end 

lemma encard_mono : monotone (encard : set α → ℕ∞) :=
λ _ _, encard_subset_le 

lemma encard_image_of_injective {α β : Type*} {f : α → β} (s : set α) (hf : f.injective) : 
  (f '' s).encard = s.encard  :=
begin
  obtain (hs | hs) := s.finite_or_infinite,
  { rw [hs.encard_eq, (hs.image f).encard_eq, ncard_image_of_injective s hf] },
  rw [hs.encard_eq, infinite.encard_eq], 
  rwa infinite_image_iff (hf.inj_on _), 
end

lemma encard_preimage_of_injective_subset_range {α β : Type*} {f : α → β} {s : set β}
  (hf : f.injective) (hs : s ⊆ range f) : (f ⁻¹' s).encard = s.encard :=
begin
  obtain ⟨t, rfl⟩ := subset_range_iff_exists_image_eq.mp hs, 
  rw [← encard_image_of_injective _ hf, preimage_image_eq _ hf], 
end

end set

end ncard

section image -- taken from mathlib.data.set.image.lean

variables {α β : Type*} {f : α → β}

@[simp] lemma subtype.preimage_image_coe (s : set α) (x : set s) : 
  (coe ⁻¹' (coe '' x : set α) : set s) = x := preimage_image_eq x subtype.coe_injective

@[simp] lemma subtype.image_coe_eq_image_coe_iff (s : set α) (x y : set s) : 
  (coe '' x : set α) = coe '' y ↔ x = y := 
image_eq_image subtype.coe_injective

end image

section basic -- taken from mathlib.data.set.basic.lean

variables {α : Type*} {s t r : set α} {a : α}

namespace set

lemma singleton_inter_eq_of_mem {x : α} (hx : x ∈ s) :
  {x} ∩ s = {x} :=
(inter_subset_left _ _).antisymm (subset_inter subset_rfl (singleton_subset_iff.mpr hx))

@[simp] lemma not_mem_diff_singleton {α : Type*} (x : α) (s : set α) :
  x ∉ s \ {x} :=
not_mem_diff_of_mem $ mem_singleton _

lemma ssubset_iff_subset_diff_singleton {α : Type*} {s t : set α} :
  s ⊂ t ↔ ∃ x ∈ t, s ⊆ t \ {x} :=
begin
  refine ⟨λ h, _,_⟩, 
  { obtain ⟨x,hxt,hxs⟩ := exists_of_ssubset h,  
    refine ⟨x, hxt, subset_diff_singleton h.subset hxs⟩ },
   rintro ⟨x, hxt, hs⟩, 
  exact hs.trans_ssubset (diff_singleton_ssubset.mpr hxt), 
end 

lemma inter_subset_union (s t : set α) : s ∩ t ⊆ s ∪ t := 
(inter_subset_left _ _).trans (subset_union_left _ _)  

/-- `r` is an explicit parameter here for ease of rewriting. -/
lemma diff_subset_diff_iff (r : set α) (hs : s ⊆ r) (ht : t ⊆ r) : (r \ s) ⊆ (r \ t) ↔ t ⊆ s :=
begin
  rw [subset_diff, and_iff_right (diff_subset _ _), ←subset_compl_iff_disjoint_left, diff_eq, 
    compl_inter, compl_compl], 
  exact ⟨λ h x hxt, (h hxt).elim (λ h', (h' (ht hxt)).elim) id, 
    λ h, h.trans (subset_union_right _ _)⟩,
end 

lemma diff_eq_diff_iff_inter_eq_inter : r \ s = r \ t ↔ r ∩ s = r ∩ t := 
by simp only [set.ext_iff, mem_diff, and.congr_right_iff, mem_inter_iff, not_iff_not]

lemma diff_eq_diff_iff_eq (hsr : s ⊆ r) (htr : t ⊆ r) : r \ s = r \ t ↔ s = t := 
by rw [diff_eq_diff_iff_inter_eq_inter, inter_eq_self_of_subset_right hsr, 
  inter_eq_self_of_subset_right htr]

@[simp] lemma diff_inter_diff_right (s t r : set α) : (s \ r) ∩ (t \ r) = (s ∩ t) \ r := 
by { ext, simp only [mem_inter_iff, mem_diff], tauto }

lemma inter_diff_right_comm (s t r : set α) : s ∩ t \ r = (s \ r) ∩ t := 
by rw [diff_eq, inter_right_comm, ←diff_eq]

end set

end basic