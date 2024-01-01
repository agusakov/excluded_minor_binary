/-
Code copied from https://github.com/apnelson1/lean-matroids
-/
import .matroid

variables {α : Type*} {M : matroid α} {k a b c : ℕ} {I J X C B E : set α}

open set 

namespace matroid 

section delete

variables {D Y Z R : set α} {e : α} {N : matroid α} 

variables {D₁ D₂ : set α}

class has_delete (α β : Type*) := (del : α → β → α)

infix ` ⟍ ` :75 :=  has_delete.del 

def delete (M : matroid α) (D : set α) : matroid α := M ‖ Dᶜ 

instance del_set {α : Type*} : has_delete (matroid α) (set α) := ⟨matroid.delete⟩
instance del_elem {α : Type*} : has_delete (matroid α) α := ⟨λ M e, M.delete {e}⟩ 

@[simp] lemma delete_compl (M : matroid α) (R : set α) : M ⟍ Rᶜ = M ‖ R := 
by { change M ‖ Rᶜᶜ = M ‖ R, rw compl_compl } 

@[simp] lemma restrict_compl (M : matroid α) (D : set α) : M ‖ Dᶜ = M ⟍ D := rfl   

@[simp] lemma restrict_ground_diff (M : matroid α) (D : set α) : M ‖ (M.E \ D) = M ⟍ D :=
by rw [←restrict_compl, ← M.restrict_inter_ground Dᶜ, diff_eq_compl_inter]

@[simp] lemma delete_ground (M : matroid α) (D : set α) : (M ⟍ D).E = M.E \ D := 
by rw [←restrict_compl, restrict_ground_eq', diff_eq_compl_inter]

@[ssE_finish_rules] lemma delete_ground_subset_ground (M : matroid α) (D : set α) : 
  (M ⟍ D).E ⊆ M.E := (M.delete_ground D).trans_subset (diff_subset _ _)

@[simp] lemma delete_elem (M : matroid α) (e : α) : M ⟍ e = M ⟍ ({e} : set α) := rfl 

@[simp] lemma delete_delete (M : matroid α) (D₁ D₂ : set α) : (M ⟍ D₁) ⟍ D₂ = M ⟍ (D₁ ∪ D₂) :=
by rw [←restrict_compl, ←restrict_compl, ←restrict_compl, restrict_restrict, compl_union]

lemma delete_eq_delete_iff : M ⟍ D₁ = M ⟍ D₂ ↔ D₁ ∩ M.E = D₂ ∩ M.E := 
by simp_rw [←restrict_compl, restrict_eq_restrict_iff,
    ←diff_eq_compl_inter, diff_eq_diff_iff_inter_eq_inter, inter_comm M.E]

lemma delete_eq_delete_inter_ground (M : matroid α) (D : set α) : M ⟍ D = M ⟍ (D ∩ M.E) := 
by rw [delete_eq_delete_iff, inter_assoc, inter_self]

lemma delete_eq_self_iff : M ⟍ D = M ↔ disjoint D M.E := 
by rw [←restrict_compl, restrict_eq_self_iff, subset_compl_iff_disjoint_left]

@[simp] lemma delete_indep_iff : (M ⟍ D).indep I ↔ M.indep I ∧ disjoint I D := 
by rw [←restrict_compl, restrict_indep_iff, subset_compl_iff_disjoint_right]

lemma indep.of_delete (h : (M ⟍ D).indep I) : M.indep I := 
(delete_indep_iff.mp h).1

lemma indep.indep_delete_of_disjoint (h : M.indep I) (hID : disjoint I D) : (M ⟍ D).indep I := 
delete_indep_iff.mpr ⟨h, hID⟩ 

@[simp] lemma delete_base_iff : (M ⟍ D).base B ↔ M.basis B (M.E \ D) :=
by rw [←restrict_compl, ←restrict_inter_ground, ←diff_eq_compl_inter, restrict_base_iff]

@[simp] lemma delete_basis_iff : (M ⟍ D).basis I X ↔ M.basis I X ∧ disjoint X D := 
begin
  simp_rw [basis_iff', delete_indep_iff, delete_ground, subset_diff, and_assoc, 
    and.congr_right_iff, and_imp, ←and_assoc, and.congr_left_iff], 
  refine λ hI hdj hX, ⟨λ h, ⟨h.1.2, λ J hJ hIJ hJX, h.2 J hJ _ hIJ hJX⟩, 
    λ h, ⟨⟨_, h.1⟩,λ J hJ hJD hIJ hJX, h.2 J hJ hIJ hJX⟩⟩, 
  { exact disjoint_of_subset_left hJX hdj },
  exact disjoint_of_subset_left h.1 hdj
end   

lemma basis.to_delete (h : M.basis I X) (hX : disjoint X D) : (M ⟍ D).basis I X := 
by { rw [delete_basis_iff], exact ⟨h, hX⟩ }

@[simp] lemma delete_dep_iff : (M ⟍ D).dep X ↔ M.dep X ∧ disjoint X D :=
by { rw [dep_iff, dep_iff, delete_indep_iff, delete_ground, subset_diff], tauto! } 

@[simp] lemma delete_loop_iff : (M ⟍ D).loop e ↔ M.loop e ∧ e ∉ D :=
by rw [loop_iff_dep, delete_dep_iff, disjoint_singleton_left, loop_iff_dep]

@[simp] lemma delete_nonloop_iff : (M ⟍ D).nonloop e ↔ M.nonloop e ∧ e ∉ D :=
by rw [←indep_singleton, delete_indep_iff, disjoint_singleton_left, indep_singleton]

@[simp] lemma delete_circuit_iff : (M ⟍ D).circuit C ↔ M.circuit C ∧ disjoint C D :=
begin
  simp_rw [circuit_iff, delete_dep_iff, and_imp], 
  rw [and_comm, ←and_assoc, and.congr_left_iff, and_comm, and.congr_right_iff],  
  refine λ hdj hC, ⟨λ h I hI hIC, h I hI _ hIC, λ h I hI hdj' hIC, h I hI hIC⟩,
  exact disjoint_of_subset_left hIC hdj, 
end  

lemma fund_circuit_delete (hI : M.indep I) (heI : e ∈ M.cl I) 
  (hdj : disjoint (insert e I) D) : (M ⟍ D).fund_circuit e I = M.fund_circuit e I :=
begin
  by_cases e ∈ I,
  { rw [hI.fund_circuit_eq_of_mem h, (delete_indep_iff.2 ⟨hI, 
      disjoint_of_subset_left (subset_insert e I) hdj⟩).fund_circuit_eq_of_mem h] },
  have hC : (M ⟍ D).circuit (M.fund_circuit e I),
  { rw [delete_circuit_iff, and_iff_right (hI.fund_circuit_circuit ((mem_diff e).2 ⟨heI, h⟩))],
    exact disjoint_of_subset_left (fund_circuit_subset_insert ((mem_diff e).2 ⟨heI, h⟩).1) hdj },

  refine (hC.eq_fund_circuit_of_subset_insert_indep _ (fund_circuit_subset_insert 
    ((mem_diff e).2 ⟨heI, h⟩).1)).symm,
  rw [delete_indep_iff],
  exact ⟨hI, disjoint_of_subset_left (subset_insert _ _) hdj⟩ 
end 

@[simp] lemma delete_cl_eq (M : matroid α) (D X : set α) : (M ⟍ D).cl X = M.cl (X \ D) \ D :=
begin
  obtain ⟨I, hI⟩ := (M ⟍ D).exists_basis ((X \ D) ∩ (M ⟍ D).E), 
  simp_rw [delete_ground, diff_eq, inter_assoc, inter_comm Dᶜ, inter_assoc, inter_self, 
    ←inter_assoc] at hI,  
  rw [cl_eq_cl_inter_ground, delete_ground, diff_eq, ←inter_assoc, ←hI.cl], 
  have hI' := (delete_basis_iff.mp hI).1, 
  
  rw [M.cl_eq_cl_inter_ground, diff_eq X D, inter_right_comm, ←hI'.cl, set.ext_iff], 
  simp_rw [hI.indep.mem_cl_iff', mem_diff, hI'.indep.mem_cl_iff', delete_ground, mem_diff, 
    delete_indep_iff, and_assoc, and.congr_right_iff, and_comm (_ ∉ D), and.congr_left_iff, 
    and_imp, ←union_singleton, disjoint_union_left, disjoint_singleton_left, union_singleton ], 

  refine λ e heE heD, _,  
  rw [iff_true_intro (disjoint_of_subset_left hI'.subset _), iff_true_intro heD], 
  { simp },
  rw ←diff_eq, exact disjoint_sdiff_left,  
end 

lemma delete_loops_eq : (M ⟍ D).cl ∅ = M.cl ∅ \ D :=
by simp only [delete_cl_eq, empty_diff]

lemma delete_er_eq' (M : matroid α) (D X : set α) : (M ⟍ D).er X = M.er (X \ D) :=
begin
  rw [delete_eq_delete_inter_ground, er_eq_er_inter_ground, delete_ground, diff_inter_self_eq_diff, 
    diff_eq, inter_comm M.E, ← inter_assoc, ←diff_eq, M.er_eq_er_inter_ground ( X \ D)],  
  obtain ⟨I, hI⟩ := M.exists_basis ((X \ D) ∩ M.E), 
  rw [←(hI.to_delete (disjoint_of_subset (inter_subset_left _ _) (inter_subset_left _ _) 
    disjoint_sdiff_left)).encard, ←hI.encard],
end 

@[simp] lemma delete_empty (M : matroid α) : M ⟍ (∅ : set α) = M := 
by { rw [delete_eq_self_iff], exact empty_disjoint _ }

noncomputable def delete_iso {β : Type*} {N : matroid β} (i : M ≃i N) (D : set α) : 
  M ⟍ D ≃i (N ⟍ i.image D) := 
(iso.cast (M.restrict_ground_diff D).symm).trans 
  ((restrict_iso i _).trans 
  (iso.cast (by rw [i.image_ground_diff, restrict_ground_diff] )))

end delete

section contract

variables {C₁ C₂ : set α}

class has_contract (α β : Type*) := (con : α → β → α)

infix ` ⟋ ` :75 :=  has_contract.con

def contract (M : matroid α) (C : set α) : matroid α := (M﹡ ⟍ C)﹡

instance con_set {α : Type*} : has_contract (matroid α) (set α) := ⟨matroid.contract⟩
instance con_elem {α : Type*} : has_contract (matroid α) α := ⟨λ M e, M.contract {e}⟩ 

@[simp] lemma dual_delete_dual_eq_contract (M : matroid α) (X : set α) : (M﹡ ⟍ X)﹡ = M ⟋ X := 
rfl  

@[simp] lemma contract_dual_eq_dual_delete (M : matroid α) (X : set α) : (M ⟋ X)﹡ = M﹡ ⟍ X :=
by rw [←dual_delete_dual_eq_contract, dual_dual]

@[simp] lemma contract_ground (M : matroid α) (C : set α) : (M ⟋ C).E = M.E \ C := 
by rw [←dual_delete_dual_eq_contract, dual_ground, delete_ground, dual_ground]

@[ssE_finish_rules] lemma contract_ground_subset_ground (M : matroid α) (C : set α) : 
  (M ⟋ C).E ⊆ M.E  := (M.contract_ground C).trans_subset (diff_subset _ _)

@[simp] lemma dual_contract_dual_eq_delete (M : matroid α) (X : set α) : (M﹡ ⟋ X)﹡ = M ⟍ X := 
by rw [←dual_delete_dual_eq_contract, dual_dual, dual_dual]

@[simp] lemma delete_dual_eq_dual_contract (M : matroid α) (X : set α) : (M ⟍ X)﹡ = M﹡ ⟋ X :=
by rw [←dual_delete_dual_eq_contract, dual_dual]

@[simp] lemma contract_elem (M : matroid α) (e : α) : M ⟋ e = M ⟋ ({e} : set α) := rfl  

@[simp] lemma contract_contract (M : matroid α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) := 
by rw [eq_comm, ←dual_delete_dual_eq_contract, ←delete_delete, ←dual_contract_dual_eq_delete, 
    ←dual_contract_dual_eq_delete, dual_dual, dual_dual, dual_dual]

lemma indep.contract_base_iff (hI : M.indep I) : (M ⟋ I).base B ↔ disjoint B I ∧ M.base (B ∪ I) := 
begin
  have hIE := hI.subset_ground, 
  rw [←dual_dual M, dual_indep_iff_coindep, coindep_iff_exists] at hI, 
  obtain ⟨B₀, hB₀, hfk⟩ := hI, 
  rw [←dual_dual M, ←dual_delete_dual_eq_contract, dual_base_iff', dual_base_iff', 
    delete_base_iff, dual_dual, delete_ground, diff_diff, union_comm, union_subset_iff, 
     subset_diff, and_comm (disjoint _ _), ← and_assoc, 
    and.congr_left_iff, dual_ground, and_iff_left hIE, and.congr_left_iff], 

  exact λ hIB hBE, ⟨λ h, h.base_of_base_subset hB₀ (subset_diff.mpr ⟨hB₀.subset_ground, hfk.symm⟩), 
    λ hB, hB.basis_of_subset (diff_subset _ _) (diff_subset_diff_right (subset_union_right _ _))⟩,
end  

lemma indep.contract_indep_iff (hI : M.indep I) : 
  (M ⟋ I).indep J ↔ disjoint J I ∧ M.indep (J ∪ I)  :=
begin
  simp_rw [indep_iff_subset_base, hI.contract_base_iff, union_subset_iff], 
  split, 
  { rintro ⟨B, ⟨hdj, hBI⟩, hJB⟩, 
    exact ⟨disjoint_of_subset_left hJB hdj, _, hBI, hJB.trans (subset_union_left _ _), 
      (subset_union_right _ _)⟩ },
  rintro ⟨hdj, B, hB, hJIB⟩, 
  refine ⟨B \I, ⟨disjoint_sdiff_left, _⟩, _⟩,
  { rwa [diff_union_self, union_eq_self_of_subset_right hJIB.2] }, 
  rw [subset_diff], 
  exact ⟨hJIB.1, hdj⟩, 
end 

lemma indep.union_indep_iff_contract_indep (hI : M.indep I) : 
  M.indep (I ∪ J) ↔ (M ⟋ I).indep (J \ I) :=
by rw [hI.contract_indep_iff, and_iff_right disjoint_sdiff_left, diff_union_self, union_comm] 

lemma indep.contract_dep_iff (hI : M.indep I) : 
  (M ⟋ I).dep J ↔ disjoint J I ∧ M.dep (J ∪ I) :=
begin
  rw [dep_iff, hI.contract_indep_iff, dep_iff, contract_ground, subset_diff, 
    disjoint.comm, union_subset_iff, and_iff_left hI.subset_ground], 
  tauto!, 
end  

lemma contract_eq_delete_of_subset_coloops (hX : X ⊆ M﹡.cl ∅) : M ⟋ X = M ⟍ X :=
begin
  refine eq_of_indep_iff_indep_forall rfl (λ I hI, _), 
  rw [(indep_of_subset_coloops hX).contract_indep_iff, delete_indep_iff, and_comm, 
    union_indep_iff_indep_of_subset_coloops hX], 
end 

lemma contract_eq_self_iff : M ⟋ C = M ↔ disjoint C M.E := 
by rw [←dual_delete_dual_eq_contract, ←dual_inj_iff, dual_dual, delete_eq_self_iff, dual_ground]

@[simp] lemma contract_empty (M : matroid α) : M ⟋ (∅ : set α) = M := 
by { rw [contract_eq_self_iff], exact empty_disjoint _, }

lemma contract_eq_contract_inter_ground (M : matroid α) (C : set α) : M ⟋ C = M ⟋ (C ∩ M.E) := 
by rw [←dual_delete_dual_eq_contract, delete_eq_delete_inter_ground, dual_delete_dual_eq_contract, 
  dual_ground]

lemma contract_eq_delete_of_subset_loops (hX : X ⊆ M.cl ∅) : M ⟋ X = M ⟍ X :=
begin
  rw [←dual_inj_iff, contract_dual_eq_dual_delete, delete_dual_eq_dual_contract, 
    eq_comm, contract_eq_delete_of_subset_coloops], 
  rwa dual_dual, 
end

lemma basis.contract_eq_contract_delete (hI : M.basis I X) : M ⟋ X = M ⟋ I ⟍ (X \ I) := 
begin
  nth_rewrite 0 ←diff_union_of_subset hI.subset, 
  rw [union_comm, ←contract_contract],  
  refine contract_eq_delete_of_subset_loops (λ e he, _), 
  have heE : e ∈ (M ⟋ I).E, from ⟨he.2,hI.subset_ground he.1⟩,
  rw [←loop_iff_mem_cl_empty, loop_iff_not_indep heE, hI.indep.contract_indep_iff, 
    disjoint_singleton_left, and_iff_right he.2, singleton_union], 
  apply dep.not_indep _, 
  rw [←hI.indep.mem_cl_iff_of_not_mem he.2, hI.cl],
  exact M.mem_cl_of_mem he.1,  
end 

lemma exists_eq_contract_indep_delete (M : matroid α) (C : set α) : 
  ∃ (I D : set α), M.basis I (C ∩ M.E) ∧ D ⊆ (M ⟋ I).E ∧ D ⊆ C ∧ M ⟋ C = M ⟋ I ⟍ D := 
begin
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E), 
  use [I, (C \ I) ∩ M.E, hI],
  rw [contract_ground, and_iff_right ((inter_subset_left _ _).trans (diff_subset _ _)), 
    diff_eq, diff_eq, inter_right_comm, inter_assoc, 
    and_iff_right (inter_subset_right _ _), contract_eq_contract_inter_ground, 
    hI.contract_eq_contract_delete, diff_eq, inter_assoc], 
  apply is_trans.swap, 
end 

lemma indep.of_contract (hI : (M ⟋ C).indep I) : M.indep I := 
begin
  obtain ⟨J, R, hJ, -, -, hM⟩ := M.exists_eq_contract_indep_delete C, 
  rw [hM, delete_indep_iff, hJ.indep.contract_indep_iff] at hI, 
  exact hI.1.2.subset (subset_union_left _ _), 
end 

@[simp] lemma contract_loop_iff_mem_cl {e : α} : (M ⟋ C).loop e ↔ e ∈ M.cl C \ C := 
begin
  obtain ⟨I, D, hI, -, hD, hM⟩ := M.exists_eq_contract_indep_delete C, 
  rw [hM, delete_loop_iff, loop_iff_dep, hI.indep.contract_dep_iff, disjoint_singleton_left, 
    singleton_union, hI.indep.insert_dep_iff, mem_diff, M.cl_eq_cl_inter_ground C, 
    hI.cl, and_comm (e ∉ I), and_self_right, ←mem_diff, ←mem_diff, diff_diff],  
  apply_fun matroid.E at hM, 
  rw [delete_ground, contract_ground, contract_ground, 
    diff_diff, diff_eq_diff_iff_inter_eq_inter, inter_comm, inter_comm M.E] at hM, 
  exact ⟨λ h, ⟨h.1, λ heC, h.2 (hM.subset ⟨heC, (M.cl_subset_ground _ h.1)⟩).1⟩, 
    λ h, ⟨h.1, λ h', h.2 (hM.symm.subset ⟨h', M.cl_subset_ground _ h.1 ⟩).1⟩⟩,
end 

@[simp] lemma contract_cl_eq (M : matroid α) (C X : set α) : (M ⟋ C).cl X = M.cl (X ∪ C) \ C :=
begin
  ext e, 
  by_cases heX : e ∈ X, 
  { by_cases he : e ∈ (M ⟋ C).E, 
    { refine iff_of_true (mem_cl_of_mem' _ heX) _,
      rw [contract_ground] at he,  
      exact ⟨mem_cl_of_mem' _ (or.inl heX) he.1, he.2⟩ },
    refine iff_of_false (he ∘ (λ h, cl_subset_ground _ _ h)) (he ∘ (λ h, _)), 
    rw [contract_ground], 
    exact ⟨M.cl_subset_ground _ h.1, h.2⟩ },
  suffices h' : e ∈ (M ⟋ C).cl X \ X ↔ e ∈ M.cl (X ∪ C) \ (X ∪ C), 
  { rwa [mem_diff, and_iff_left heX, mem_diff, mem_union, or_iff_right heX, ←mem_diff ] at h' },  
  rw [←contract_loop_iff_mem_cl, ←contract_loop_iff_mem_cl, contract_contract, union_comm], 
end 

lemma contract_loops_eq : (M ⟋ C).cl ∅ = M.cl C \ C := 
by simp_rw [set.ext_iff, ←loop_iff_mem_cl_empty, contract_loop_iff_mem_cl, iff_self, 
  implies_true_iff]

lemma contract_eq_contract_iff : M ⟋ C₁ = M ⟋ C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := 
by rw [←dual_delete_dual_eq_contract, ←dual_delete_dual_eq_contract, dual_inj_iff, 
  delete_eq_delete_iff, dual_ground]

lemma coindep_contract_iff : (M ⟋ C).coindep X ↔ M.coindep X ∧ disjoint X C :=
by rw [←dual_indep_iff_coindep, contract_dual_eq_dual_delete, delete_indep_iff, 
  dual_indep_iff_coindep]

/-- This lemma is useful where it is known (or unimportant) that `X ⊆ M.E` -/
lemma er_contract_eq_er_contract_diff (M : matroid α) (C X : set α) :
  (M ⟋ C).er X = (M ⟋ C).er (X \ C) :=
by rw [←er_cl, contract_cl_eq, ←er_cl _ (X \ C), contract_cl_eq, diff_union_self]

/-- This lemma is useful where it is known (or unimportant) that `X` and `C` are disjoint -/
lemma er_contract_eq_er_contract_inter_ground (M : matroid α) (C X : set α) : 
  (M ⟋ C).er X = (M ⟋ C).er (X ∩ M.E) := 
by rw [er_eq_er_inter_ground, contract_ground, M.er_contract_eq_er_contract_diff _ (X ∩ M.E), 
    inter_diff_assoc]

lemma basis.contract_basis_union_union (h : M.basis (J ∪ I) (X ∪ I)) (hdj : disjoint (J ∪ X) I)  : 
  (M ⟋ I).basis J X :=
begin
  rw [disjoint_union_left] at hdj, 
  have hI := h.indep.subset (subset_union_right _ _), 
  simp_rw [basis, mem_maximals_set_of_iff, hI.contract_indep_iff, and_iff_right hdj.1, 
    and_iff_right h.indep, contract_ground, subset_diff, and_iff_left hdj.2, 
    and_iff_left ((subset_union_left _ _).trans h.subset_ground), and_imp, 
    and_iff_right 
      (disjoint.subset_left_of_subset_union ((subset_union_left _ _).trans h.subset) hdj.1)], 
  intros Y hYI hYi hYX hJY, 
  have hu := 
    h.eq_of_subset_indep hYi (union_subset_union_left _ hJY) (union_subset_union_left _ hYX), 
  apply_fun (λ (x : set α), x \ I) at hu, 
  simp_rw [union_diff_right, hdj.1.sdiff_eq_left, hYI.sdiff_eq_left] at hu, 
  exact hu, 
end 

/-- This lemma is essentially defining the 'relative rank' of `X` to `C`. The required set `I` can 
  be obtained for any `X,C ⊆ M.E` using `M.exists_basis_union_inter_basis X C`. -/
lemma basis.er_contract (hI : M.basis I (X ∪ C)) (hIC : M.basis (I ∩ C) C) : 
  (M ⟋ C).er X = (I \ C).encard :=
begin
  rw [er_contract_eq_er_contract_diff, hIC.contract_eq_contract_delete, delete_er_eq', 
    diff_inter_self_eq_diff, basis.encard],
  apply basis.contract_basis_union_union, 
  { rw [diff_union_inter, diff_diff, union_eq_self_of_subset_right (diff_subset _ _)], 
    apply hI.basis_subset _ (union_subset_union (diff_subset _ _) (inter_subset_right _ _)),
    rw [union_comm, ←diff_subset_iff, subset_diff, diff_self_inter, diff_subset_iff, union_comm], 
    exact ⟨hI.subset, disjoint_sdiff_left⟩ }, 
  rw [disjoint_union_left], 
  exact ⟨disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left, 
    disjoint_of_subset (diff_subset _ _) (inter_subset_right _ _) disjoint_sdiff_left⟩, 
end 

lemma er_contract_add_er_eq_er_union (M : matroid α) (C X : set α) : 
  (M ⟋ C).er X + M.er C = M.er (X ∪ C) :=
begin
  obtain ⟨I, D, hIC, hD, hDC, hM⟩ := M.exists_eq_contract_indep_delete C, 
  obtain ⟨J, hJ, rfl⟩ :=
    hIC.exists_basis_inter_eq_of_supset (subset_union_right (X ∩ M.E) _) (by simp), 
  rw [er_contract_eq_er_contract_inter_ground, contract_eq_contract_inter_ground, 
    hJ.er_contract hIC, er_eq_er_inter_ground, ←hIC.encard, er_eq_er_inter_ground,
    inter_distrib_right, ←hJ.encard, encard_diff_add_encard_inter], 
end  

lemma basis.diff_subset_loops_contract (hIX : M.basis I X) : X \ I ⊆ (M ⟋ I).cl ∅ :=
begin
  rw [diff_subset_iff, contract_loops_eq, union_diff_self, 
    union_eq_self_of_subset_left (M.subset_cl I)], 
  exact hIX.subset_cl
end 

noncomputable def contract_iso {β : Type*} {N : matroid β} (i : M ≃i N) (C : set α) : 
  M ⟋ C ≃i (N ⟋ i.image C) := 
(delete_iso i.dual C).dual

end contract

section minor

variables {N M₀ M₁ M₂ : matroid α} {D : set α}

lemma contract_delete_diff (M : matroid α) (C D : set α) : M ⟋ C ⟍ D = M ⟋ C ⟍ (D \ C) := 
by rw [delete_eq_delete_iff, contract_ground, diff_eq, diff_eq, ←inter_inter_distrib_right, 
  inter_assoc]

lemma contract_delete_comm (M : matroid α) {C D : set α} (hCD : disjoint C D) : 
  M ⟋ C ⟍ D = M ⟍ D ⟋ C := 
begin
  rw [contract_eq_contract_inter_ground, (M ⟍ D).contract_eq_contract_inter_ground, 
    delete_ground, inter_diff_distrib_left, hCD.inter_eq, diff_empty], 
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E), 
  have hI' : (M ⟍ D).basis I (C ∩ M.E), 
  { rw delete_basis_iff, exact ⟨hI, disjoint_of_subset_left (inter_subset_left _ _) hCD⟩ },
  have hID : disjoint I D, 
  { refine disjoint_of_subset_left hI'.subset_ground_left _, simp [disjoint_sdiff_left] },
  rw [hI.contract_eq_contract_delete, hI'.contract_eq_contract_delete],
  refine eq_of_indep_iff_indep_forall _ (λ J hJ, _), 
  { ext, simp only [delete_delete, delete_ground, contract_ground, mem_diff, mem_union, 
      mem_inter_iff, not_and, not_not_mem, and_imp], tauto! },
  
  simp only [hI.indep.contract_indep_iff, hI'.indep.contract_indep_iff, delete_delete, 
    delete_indep_iff, disjoint_union_right, disjoint_union_left, and_assoc, 
    and_comm _ (disjoint J D), and.congr_right_iff, iff_and_self, iff_true_intro hID, 
    imp_true_iff], 
end 

lemma delete_contract_diff (M : matroid α) (D C : set α) : M ⟍ D ⟋ C = M ⟍ D ⟋ (C \ D) :=
by rw [contract_eq_contract_iff, delete_ground, diff_inter_diff_right, diff_eq, diff_eq, 
  inter_assoc]

lemma contract_delete_contract' (M : matroid α) (C D C' : set α) :
  M ⟋ C ⟍ D ⟋ C' = M ⟋ (C ∪ C' \ D) ⟍ D :=
by rw [delete_contract_diff, ←contract_delete_comm _ disjoint_sdiff_left, contract_contract]

lemma contract_delete_contract (M : matroid α) (C D C' : set α) (h : disjoint C' D) :
  M ⟋ C ⟍ D ⟋ C' = M ⟋ (C ∪ C') ⟍ D := 
by rw [contract_delete_contract', sdiff_eq_left.mpr h] 

lemma contract_delete_contract_delete' (M : matroid α) (C D C' D' : set α) : 
  M ⟋ C ⟍ D ⟋ C' ⟍ D' = M ⟋ (C ∪ C' \ D) ⟍ (D ∪ D') :=
by rw [contract_delete_contract', delete_delete]

def minor (N M : matroid α) : Prop := ∃ (C ⊆ M.E) (D ⊆ M.E), disjoint C D ∧ N = M ⟋ C ⟍ D

infix ` ≤m ` :75 :=  matroid.minor

lemma contract_delete_minor (M : matroid α) (C D : set α) : M ⟋ C ⟍ D ≤m M := 
begin
  rw [contract_delete_diff, contract_eq_contract_inter_ground, delete_eq_delete_inter_ground, 
    contract_ground, diff_inter_self_eq_diff, diff_inter_diff_right, inter_diff_right_comm],
  refine ⟨_, inter_subset_right _ _, _, inter_subset_right _ _, _, rfl⟩,
  refine disjoint_of_subset (inter_subset_left _ _) _ (disjoint_compl_right),  
  rw [diff_eq, inter_right_comm], 
  exact inter_subset_right _ _, 
end    

instance minor_refl : is_refl (matroid α) (≤m) := 
⟨λ M, ⟨∅, empty_subset _, ∅, empty_subset _, empty_disjoint _, by simp⟩⟩   

instance minor_antisymm : is_antisymm (matroid α) (≤m) := 
begin
  constructor, 
  rintro M M' ⟨C,hC,D,hD,hCD,h⟩ ⟨C',hC',D',hD',hCD',h'⟩, 
  have h'' := h', 
  apply_fun E at h', 
  simp_rw [delete_ground, contract_ground, h, delete_ground, contract_ground, diff_diff] at h', 
  rw [eq_comm, sdiff_eq_left, disjoint_union_right, disjoint_union_right, 
    disjoint_union_right] at h', 
  have hC : C = ∅ := h'.1.1.1.eq_bot_of_ge hC, subst hC, 
  have hD : D = ∅ := h'.1.1.2.eq_bot_of_ge hD, subst hD, 
  rwa [delete_empty, contract_empty] at h,
end 

instance minor_trans : is_trans (matroid α) (≤m) := 
begin
  constructor, 
  rintros M₁ M₂ M₃ ⟨C₁,hC₁,D₁,hD₁,hdj,rfl⟩ ⟨C₂,hC₂,D₂,hD₂,hdj',rfl⟩, 
  rw [contract_delete_contract_delete'], 
  apply contract_delete_minor, 
end 

lemma minor.refl {M : matroid α} : M ≤m M :=
refl M   

lemma minor.trans {M₁ M₂ M₃ : matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ :=
trans h h' 

lemma minor.antisymm (h : N ≤m M) (h' : M ≤m N) : N = M := 
antisymm h h' 

lemma contract_minor (M : matroid α) (C : set α) : M ⟋ C ≤m M := 
by { rw ←(M ⟋ C).delete_empty, apply contract_delete_minor } 

lemma delete_minor (M : matroid α) (D : set α) : M ⟍ D ≤m M := 
by { nth_rewrite 0 [←M.contract_empty], apply contract_delete_minor }

lemma minor.ground_subset (h : N ≤m M) : N.E ⊆ M.E := 
begin
  obtain ⟨C, hC, D, hD, hCD, rfl⟩ := h, 
  simp only [delete_ground, contract_ground], 
  exact (diff_subset _ _).trans (diff_subset _ _), 
end 

/-- The scum theorem. We can always realize a minor by contracting an independent set and deleting
  a coindependent set -/
theorem minor.exists_contract_indep_delete_coindep (h : N ≤m M) : 
  ∃ C D, M.indep C ∧ M.coindep D ∧ disjoint C D ∧ N = M ⟋ C ⟍ D :=
begin
  obtain ⟨C', hC', D', hD', hCD', rfl⟩ := h, 
  obtain ⟨I, hI⟩ := M.exists_basis C',  
  obtain ⟨K, hK⟩ := M﹡.exists_basis D', 
  have hIK : disjoint I K, from disjoint_of_subset hI.subset hK.subset hCD', 
  use [I ∪ (D' \ K), (C' \ I) ∪ K], 
  refine ⟨_,_,_,_⟩, 
  { have hss : D' \ K \ I ⊆ (M﹡ ⟋ K ⟍ I).cl ∅, 
    { rw [delete_loops_eq], exact diff_subset_diff_left hK.diff_subset_loops_contract },
    rw [←delete_dual_eq_dual_contract, ←contract_dual_eq_dual_delete ] at hss, 
    have hi := indep_of_subset_coloops hss, 
    rw [←contract_delete_comm _ hIK, delete_indep_iff, hI.indep.contract_indep_iff, 
      diff_union_self, union_comm] at hi, 
    exact hi.1.2 },
  { rw [←dual_indep_iff_coindep],
    have hss : C' \ I \ K ⊆ (M ⟋ I ⟍ K)﹡﹡.cl ∅, 
    { rw [dual_dual, delete_loops_eq], exact diff_subset_diff_left hI.diff_subset_loops_contract }, 
    have hi := indep_of_subset_coloops hss, 
    rw [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete, 
      ←contract_delete_comm _ hIK.symm, delete_indep_iff, hK.indep.contract_indep_iff, 
      diff_union_self] at hi, 
    exact hi.1.2 },
  { rw [disjoint_union_left, disjoint_union_right, disjoint_union_right, 
      and_iff_right disjoint_sdiff_right, and_iff_right hIK, and_iff_left disjoint_sdiff_left],
    exact disjoint_of_subset (diff_subset _ _) (diff_subset _ _) hCD'.symm },
  have hb : (M ⟋ C')﹡.basis K D', 
  { rw [contract_dual_eq_dual_delete, delete_basis_iff, and_iff_right hK],
    exact hCD'.symm },
  rw [←dual_dual (M ⟋ C' ⟍ D'), delete_dual_eq_dual_contract, hb.contract_eq_contract_delete, 
    hI.contract_eq_contract_delete, delete_dual_eq_dual_contract, contract_dual_eq_dual_delete, 
    dual_dual, delete_delete, contract_delete_contract], 
  rw [disjoint_union_right, and_iff_left disjoint_sdiff_left], 
  exact disjoint_of_subset (diff_subset _ _) (diff_subset _ _) hCD'.symm, 
end   

theorem minor.eq_of_ground_subset (h : N ≤m M) (hE : M.E ⊆ N.E) : M = N := 
begin
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep, 
  simp only [delete_ground, contract_ground] at hE, 
  rw [subset_diff, subset_diff] at hE, 
  rw [contract_eq_contract_inter_ground, hE.1.2.symm.inter_eq, contract_empty,
    delete_eq_delete_inter_ground, hE.2.symm.inter_eq, delete_empty], 
end

theorem minor.minor_contract_or_minor_delete {e : α} (h : N ≤m M) (he : e ∈ M.E \ N.E) :
    N ≤m (M ⟋ e) ∨ N ≤m (M ⟍ e) := 
begin
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep, 
  rw [delete_ground, contract_ground, diff_diff, 
    diff_diff_cancel_left (union_subset hC.subset_ground hD.subset_ground)] at he, 
  obtain (heC | heD) := he, 
  { left, 
    apply (delete_minor _ _).trans _, 
    rw [← insert_eq_self.2 heC, ← union_singleton, union_comm, ← contract_contract], 
    exact contract_minor _ _ },
  right, 
  rw [contract_delete_comm _ hCD], 
  apply (contract_minor _ _).trans _, 
  rw [← insert_eq_self.2 heD, ← union_singleton, union_comm, ← delete_delete], 
  apply delete_minor, 
end 

/-- An excluded minor is a minimal nonelement of S -/
def excluded_minor (S : set (matroid α)) (M : matroid α) := 
  M ∈ minimals (≤m) Sᶜ 

/-- A class is minor-closed if minors of matroids in the class are all in the class. -/
def minor_closed (S : set (matroid α)) : Prop := ∀ {M N}, N ≤m M → M ∈ S → N ∈ S  

lemma excluded_minor_iff (S : set (matroid α)) (hS : minor_closed S) :
  excluded_minor S M ↔ M ∉ S ∧ ∀ e ∈ M.E, M ⟋ e ∈ S ∧ M ⟍ e ∈ S :=
begin
  rw [excluded_minor, mem_minimals_iff', mem_compl_iff, and.congr_right_iff],
  intro hMS, 
  refine ⟨λ h e he, ⟨by_contra (fun hM', _),by_contra (fun hM', _)⟩, fun h N hN hNM, _⟩,
  { rw [h hM' (M.contract_minor {e}), contract_elem, contract_ground] at he, 
    exact he.2 rfl },
  { rw [h hM' (M.delete_minor _), delete_elem, delete_ground] at he, 
    exact he.2 rfl },
  refine hNM.eq_of_ground_subset (fun e heM, by_contra (fun heN, hN _)),  
  obtain (h1 | h1) := hNM.minor_contract_or_minor_delete ⟨heM, heN⟩, 
  { exact hS h1 (h e heM).1 },
  exact hS h1 (h e heM).2
end 

lemma excluded_minor.contract_mem {S : set (matroid α)} (h : excluded_minor S M)
(hC : (C ∩ M.E).nonempty) : M ⟋ C ∈ S := 
begin
  by_contra hn,
  have := ((h.2 hn (contract_minor _ _)).ground_subset).antisymm 
    (contract_ground_subset_ground M C),
  rw [contract_ground, eq_comm, sdiff_eq_left, disjoint_iff_inter_eq_empty, inter_comm] at this, 
  simpa [this] using hC,
end 

lemma excluded_minor.delete_mem {S : set (matroid α)} (h : excluded_minor S M)
(hD : (D ∩ M.E).nonempty) : M ⟍ D ∈ S := 
begin
  by_contra hn,
  have := ((h.2 hn (delete_minor _ _)).ground_subset).antisymm 
    (delete_ground_subset_ground M D),
  rw [delete_ground, eq_comm, sdiff_eq_left, disjoint_iff_inter_eq_empty, inter_comm] at this, 
  simpa [this] using hD,
end 

theorem mem_iff_no_excluded_minor_minor [M.finite] {S : set (matroid α)} (hS : minor_closed S) : 
  M ∈ S ↔ ∀ N, excluded_minor S N → ¬(N ≤m M) := 
begin
  refine ⟨λ h N hN hNM, hN.1 (hS hNM h), λ h, by_contra (λ hMS, _)⟩,
  set minground := {X : (set α)ᵒᵈ | ∃ N, N ≤m M ∧ N.E = X ∧ N ∉ S},
  have hne : minground.nonempty := ⟨M.E, M, minor.refl, rfl, hMS⟩, 
  have hfin : minground.finite,
  { refine M.ground_finite.finite_subsets.subset _,
    rintro X ⟨N, hN, rfl, h⟩, 
    exact hN.ground_subset },
  obtain ⟨X, ⟨N, hN, rfl, hNS⟩, hmax⟩ := finite.exists_maximal_wrt id _ hfin hne, 
  refine h N ⟨hNS, fun M' (hM' : M' ∉ S) hM'N, _⟩ hN, 
  have hNM' : N.E = M'.E := hmax M'.E ⟨M', (hM'N.trans hN), rfl, hM'⟩ hM'N.ground_subset,  
  rw [hM'N.eq_of_ground_subset hNM'.subset],
  exact minor.refl,
end 

end minor

section iso_minor

/-- We have `N ≤i M` if `M` has an `N`-minor; i.e. `N` is isomorphic to a minor of `M` -/
def iso_minor {β : Type*} (N : matroid β) (M : matroid α) : Prop :=
  ∃ (M' : matroid α), M' ≤m M ∧ nonempty (N ≃i M')

infix ` ≤i ` :75 :=  matroid.iso_minor

lemma iso.iso_minor {β : Type*} {N : matroid β} (e : N ≃i M) : N ≤i M :=
⟨M, minor.refl, ⟨e⟩⟩  

lemma minor.trans_iso {β : Type*} {N : matroid α} {M' : matroid β} (h : N ≤m M) (e : M ≃i M') 
  : N ≤i M' :=
begin
  obtain ⟨C, hC, D, hD, hCD, rfl⟩ := h, 
  set i := delete_iso (contract_iso e C) D, 
  exact ⟨_,contract_delete_minor _ _ _,⟨i⟩⟩, 
end 

lemma minor.iso_minor {N : matroid α} (h : N ≤m M) : N ≤i M := 
⟨N, h, ⟨iso.refl N⟩⟩ 

lemma iso_minor.trans {α₁ α₂ α₃ : Type*} {M₁ : matroid α₁} {M₂ : matroid α₂} 
{M₃ : matroid α₃} (h : M₁ ≤i M₂) (h' : M₂ ≤i M₃) : M₁ ≤i M₃ :=
begin
  obtain ⟨M₂', hM₂'M₃, ⟨i'⟩⟩ := h',
  obtain ⟨M₁', hM₁'M₂, ⟨i''⟩⟩ := h,
  obtain ⟨N, hN, ⟨iN⟩⟩ := hM₁'M₂.trans_iso i',  
  exact ⟨N, hN.trans hM₂'M₃, ⟨i''.trans iN⟩⟩, 
end 

lemma iso.trans_iso_minor {β : Type*} {N' : matroid α} {N : matroid β} 
  (e : N ≃i N') (h : N' ≤i M) : N ≤i M := 
e.iso_minor.trans h

end iso_minor

section update

variables [decidable_eq α] {β : Type*} {f : α → β} {s : set α} {a' : α} {b' : β}

lemma preimage_update  {f : α → β} (hf : f.injective) (a : α) (b : β) (s : set β) 
  [decidable (b ∈ s)] :
  (f.update a b) ⁻¹' s = if b ∈ s then insert a (f ⁻¹' (s \ {f a})) else (f ⁻¹' (s \ {f a})) := 
begin
  split_ifs, 
  { rw [subset_antisymm_iff, insert_subset, set.mem_preimage, function.update_same, 
      set.preimage_diff, and_iff_right h, diff_subset_iff, 
      (show {f a} = f '' {a}, by rw [image_singleton]), 
      preimage_image_eq _ hf, singleton_union, insert_diff_singleton],
    refine ⟨fun x hx, _, fun x hx, _⟩, 
    { obtain (rfl | hxa) := eq_or_ne x a,
      { rw [mem_preimage, function.update_same] at hx,
        apply mem_insert },
      rw [mem_preimage, function.update_noteq hxa] at hx, 
      exact mem_insert_of_mem _ hx },
    obtain (rfl | hxa) := eq_or_ne x a,
    { exact mem_insert _ _ },
    rw [mem_insert_iff, mem_preimage, function.update_noteq hxa], 
    exact or.inr hx },
  refine subset_antisymm (fun x hx, _) (fun x hx, _), 
  { obtain (rfl | hxa) := eq_or_ne x a,
    { exact (h (by simpa using hx)).elim },
    rw [mem_preimage, function.update_noteq hxa] at hx, 
    exact ⟨hx, by rwa [mem_singleton_iff, hf.eq_iff], ⟩ }, 
  rw [mem_preimage, mem_diff, mem_singleton_iff, hf.eq_iff] at hx, 
  rw [mem_preimage, function.update_noteq hx.2], 
  exact hx.1, 
end 

lemma pair_subset_iff {x y : α} {s : set α} : {x,y} ⊆ s ↔ x ∈ s ∧ y ∈ s :=
  by rw [insert_subset, singleton_subset_iff]

lemma update_inj_on_iff : 
  inj_on (f.update a' b') s ↔ inj_on f (s \ {a'}) ∧ (a' ∈ s → ∀ x ∈ s, f x = b' → x = a') :=
begin
  refine ⟨fun h, ⟨fun x hx y hy hxy, h hx.1 hy.1 _, _⟩, fun h x hx y hy hxy, _⟩,
  { rwa [function.update_noteq hx.2, function.update_noteq hy.2] },
  { rintro has x hxs rfl, 
    exact by_contra (fun hne, hne (h hxs has (by rw [function.update_same, 
      function.update_noteq hne]))) },
  obtain ⟨(rfl | hxa), (rfl | hya)⟩ := ⟨eq_or_ne x a', eq_or_ne y a'⟩, 
  { refl },
  { rw [function.update_same, function.update_noteq hya, eq_comm] at hxy, 
    rw [h.2 hx y hy hxy] },
  { rw [function.update_same, function.update_noteq hxa] at hxy,
    rw [h.2 hy x hx hxy] },
  rwa [function.update_noteq hxa, function.update_noteq hya, h.1.eq_iff ⟨hx, hxa⟩ ⟨hy,hya⟩] at hxy
end 

@[simp] lemma image_update (a : α) (f : α → β) (s : set α) (b : β) [decidable (a ∈ s)] :
  (f.update a b) '' s = if a ∈ s then insert b (f '' (s \ {a})) else f '' s :=
begin
  split_ifs, 
  { rw [subset_antisymm_iff, image_subset_iff], 
    refine ⟨λ x hxs, (em (x = a)).elim (fun heq, _) (fun hne, or.inr _), λ x, _⟩,
    { rw [mem_preimage, function.update_apply, if_pos heq]; exact mem_insert _ _ },
    { exact ⟨x, ⟨hxs, hne⟩, by rw [function.update_noteq hne]⟩ },
    rintro (rfl | ⟨x, hx, rfl⟩), 
    { use a, simpa },
    exact ⟨x, hx.1, function.update_noteq hx.2 _ _⟩ },
  rw [subset_antisymm_iff, image_subset_iff, image_subset_iff], 
  refine ⟨fun x hxs, ⟨x, hxs, _⟩, fun x hxs, ⟨x, hxs, _⟩⟩;
  { rw [function.update_noteq], exact fun hxa, h (by rwa ← hxa) },
end 

@[simp] lemma update_id_inj_on_iff {a b : α} : 
    inj_on ((@id α).update a b) s ↔ (a ∈ s → b ∈ s → a = b) := 
begin
  rw [update_inj_on_iff, and_iff_right (function.injective_id.inj_on _)], 
  refine ⟨fun h has hbs, (h has b hbs rfl).symm, _⟩, 
  rintro h has _ hbs rfl, 
  exact (h has hbs).symm, 
end 

end update

section bij_on

/-- If `f` maps `s` bijectively to `t` and, then for any `s ⊆ s₁` and `t ⊆ t' ⊆ f '' s₁`,
  there is some `s ⊆ s' ⊆ s₁` so that `f` maps `s'` bijectively to `t'`. -/
theorem set.bij_on.extend_of_subset {β : Type*} {f : α → β} {s s₁ : set α} {t t' : set β}
    (h : bij_on f s t) (hss₁ : s ⊆ s₁) (htt' : t ⊆ t') (ht' : t' ⊆ f '' s₁) :
    ∃ s', s ⊆ s' ∧ s' ⊆ s₁ ∧ bij_on f s' t' :=
begin
  have hex : ∀ (b : (t' \ t)),  ∃ a, a ∈ s₁ \ s ∧ f a = b,
  { rintro ⟨b, hb⟩,
    obtain ⟨a, ha, rfl⟩ := ht' hb.1,
    exact ⟨_, ⟨ha, fun has, hb.2 (h.maps_to has)⟩, rfl⟩ }, 
  choose g hg using hex,
  have hinj : inj_on f (s ∪ range g),
  { rw [inj_on_union, and_iff_right h.inj_on, and_iff_left],
    { rintro _ ⟨⟨x,hx⟩, rfl⟩ _ ⟨⟨x', hx'⟩,rfl⟩ hf,
      simp only [(hg _).2, (hg _).2] at hf,
      rw [subtype.coe_mk, subtype.coe_mk] at hf, 
      subst hf },
    { rintro x hx _ ⟨⟨y,hy⟩, hy', rfl⟩ h_eq,
      rw [(hg _).2] at h_eq,
      obtain (rfl : _ = y) := h_eq,
      exact hy.2 (h.maps_to hx), },
    rw [disjoint_iff_forall_ne],
    rintro x hx _ ⟨y, hy, rfl⟩ rfl,
    have h' := h.maps_to hx,
    rw [(hg _).2] at h',
    exact y.prop.2 h' },
  have hp : bij_on f (range g) (t' \ t),
  { apply bij_on.mk,
    { rintro _ ⟨x, hx, rfl⟩; rw [(hg _).2]; exact x.2}, 
    { exact hinj.mono (subset_union_right _ _), },
    exact fun x hx, ⟨g ⟨x,hx⟩, by simp [(hg _).2] ⟩,}, 
  refine ⟨s ∪ range g, subset_union_left _ _, union_subset hss₁  _, _⟩,
  { rintro _ ⟨x, hx, rfl⟩; exact (hg _).1.1 }, 
  convert h.union hp _,
  { exact (union_diff_cancel htt').symm }, 
  exact hinj,
end 

theorem set.bij_on.extend {β : Type*} {f : α → β} {s : set α} {t t' : set β} (h : bij_on f s t) 
    (htt' : t ⊆ t') (ht' : t' ⊆ range f) : ∃ s', s ⊆ s' ∧ bij_on f s' t' := by
  simpa using h.extend_of_subset (subset_univ s) htt' (by simpa)

end bij_on

section restrict

def restrict' (M : matroid α) (X : set α) : matroid α :=
matroid_of_indep X (λ I, M.indep I ∧ I ⊆ X ∩ M.E) ⟨M.empty_indep, empty_subset _⟩ 
(λ I J hJ hIJ, ⟨hJ.1.subset hIJ, hIJ.trans hJ.2⟩)
(begin
  set Y := X ∩ M.E with hY_def, 
  have hY : Y ⊆ M.E := inter_subset_right _ _, 
  rintro I I' ⟨hI, hIY⟩ hIn hI',
  rw ←basis_iff_mem_maximals at hIn hI', 
  obtain ⟨B', hB', rfl⟩ := hI'.exists_base, 
  obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB',
  
  rw [hB'.inter_basis_iff_compl_inter_basis_dual hY, diff_inter_diff] at hI', 
  
  have hss : M.E \ (B' ∪ Y) ⊆ M.E \ (B ∪ Y), 
  { rw [subset_diff, and_iff_right (diff_subset _ _), ←subset_compl_iff_disjoint_left, 
      diff_eq, compl_inter, compl_compl, ←union_assoc, union_subset_iff, 
      and_iff_left (subset_union_right _ _)],
    refine hBIB'.trans (union_subset (hIY.trans _) 
      (subset_union_of_subset_left (subset_union_right _ _) _)), 
    apply subset_union_right },

  have hi : M﹡.indep (M.E \ (B ∪ Y)), 
  { rw [dual_indep_iff_coindep, coindep_iff_exists], 
    exact ⟨B, hB, disjoint_of_subset_right (subset_union_left _ _) disjoint_sdiff_left⟩ }, 
  have h_eq := hI'.eq_of_subset_indep hi hss 
    (by {rw [diff_subset_iff, union_assoc, union_diff_self, ←union_assoc], simp }), 
  
  rw [h_eq, ←diff_inter_diff, ←hB.inter_basis_iff_compl_inter_basis_dual hY] at hI', 

  have hssu : I ⊂ (B ∩ Y) := (subset_inter hIB hIY).ssubset_of_ne 
    (by { rintro rfl, exact hIn hI' }), 

  obtain ⟨e, heBY, heI⟩ := exists_of_ssubset hssu, 
  exact ⟨e, ⟨⟨(hBIB' heBY.1).elim (λ h', (heI h').elim) id ,heBY.2⟩,heI⟩, 
    (hB.indep.inter_right Y).subset (insert_subset.mpr ⟨heBY,hssu.subset⟩), 
    insert_subset.mpr ⟨heBY.2,hssu.subset.trans (inter_subset_right _ _)⟩⟩, 
end)
(begin
  rintro X hX I ⟨hI, hIX⟩ hIA, 
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIA hIX), 
  refine ⟨J, ⟨⟨hJ.indep,hJ.subset.trans (inter_subset_right _ _)⟩,hIJ,
    hJ.subset.trans (inter_subset_left _ _)⟩, λ B hB hJB, _⟩, 
  rw hJ.eq_of_subset_indep hB.1.1 hJB (subset_inter hB.2.2 hB.1.2), 
end)
(fun I hI, hI.2.trans (inter_subset_left _ _))   

@[simp] lemma restrict'_indep_iff {M : matroid α} {X I : set α} : 
  (M.restrict' X).indep I ↔ M.indep I ∧ I ⊆ X := 
begin
  simp only [restrict', subset_inter_iff, matroid_of_indep_apply, and.congr_right_iff, 
    and_iff_left_iff_imp], 
  exact fun h _, h.subset_ground 
end 

end restrict

section preimage

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`.
  Elements with the same image are parallel and the ground set is `f ⁻¹' M.E`. -/
def preimage {β : Type*} (M : matroid β) (f : α → β) : matroid α := matroid_of_indep
  (f ⁻¹' M.E) (fun I, M.indep (f '' I) ∧ inj_on f I) ( by simp )
  ( fun I J ⟨h, h'⟩ hIJ, ⟨h.subset (image_subset _ hIJ), inj_on.mono hIJ h'⟩ )
  ( begin
    rintro I B ⟨hI, hIinj⟩ hImax hBmax,
    change I ∉ maximals _ {I : set α  | _} at hImax, 
    change B ∈ maximals _ {I : set α  | _} at hBmax, 
    simp only [mem_maximals_iff', mem_set_of_eq, hI, hIinj, and_self, and_imp,
      true_and, not_forall, exists_prop, not_and] at hImax hBmax,
    
    obtain ⟨I', hI', hI'inj, hII', hne⟩ := hImax,

    have h₁ : ¬(M.restrict' (set.range f)).base (f '' I),
    { refine fun hB, hne _,
      have h_im := hB.eq_of_subset_indep _ (image_subset _ hII'),
      { refine hII'.antisymm (fun x hxI', _), 
        rw [← hI'inj.mem_image_iff hII' hxI', h_im], 
        exact mem_image_of_mem _ hxI' },
      rwa [restrict'_indep_iff, and_iff_left (image_subset_range _ _)] }, 


    have h₂ : (M.restrict' (range f)).base (f '' B),
    { refine indep.base_of_maximal (by simpa using hBmax.1.1) (fun J hJi hBJ, _),
      simp only [restrict'_indep_iff] at hJi,
      obtain ⟨J₀, hBJ₀, hJ₀⟩ := hBmax.1.2.bij_on_image.extend hBJ hJi.2, 
      obtain rfl := hJ₀.image_eq,
      rw [hBmax.2 hJi.1 hJ₀.inj_on hBJ₀]}, 

    obtain ⟨_, ⟨⟨e, he, rfl⟩, he'⟩, hei⟩ := indep.exists_insert_of_not_base (by simpa) h₁ h₂,
    have heI : e ∉ I := fun heI, he' (mem_image_of_mem f heI),
    rw [← image_insert_eq, restrict'_indep_iff] at hei,
    exact ⟨e, ⟨he, heI⟩, hei.1, (inj_on_insert heI).2 ⟨hIinj, he'⟩⟩,
  end )
  ( begin
    
    rintro X - I ⟨hI, hIinj⟩ hIX,
    obtain ⟨J, hJ, hIJ⟩ := 
      (show (M.restrict' (range f)).indep (f '' I), by simpa).subset_basis_of_subset
      (image_subset _ hIX) (image_subset_range _ _), 
    
    simp only [basis_iff, restrict'_indep_iff] at hJ, 

    obtain ⟨J₀, hIJ₀, hJ₀X, hbij⟩ := hIinj.bij_on_image.extend_of_subset hIX hIJ hJ.2.1, 
    use J₀, 
    simp only [mem_maximals_iff', mem_set_of_eq], 
    rw [and_iff_left hbij.inj_on, hbij.image_eq, and_iff_right hJ.1.1, and_iff_right hIJ₀, 
      and_iff_right hJ₀X], 
    rintro K ⟨⟨hK, hKinj⟩, hIK, hKX⟩ hJ₀K, 
    obtain rfl := hJ.2.2 _ ⟨hK, image_subset_range _ _⟩ _ (image_subset _ hKX),  
    { refine hJ₀K.antisymm (fun x hxK, _),
      rwa [← hKinj.mem_image_iff hJ₀K hxK, hbij.image_eq, hKinj.mem_image_iff subset.rfl hxK] },
    rw [← hbij.image_eq ], 
    exact image_subset _ hJ₀K, 
  end )
  (  fun I hI e heI, hI.1.subset_ground ⟨e, heI, rfl⟩  )

@[simp] lemma preimage_ground_eq {β : Type*} (M : matroid β) (f : α → β) : 
  (M.preimage f).E = f ⁻¹' M.E := rfl

@[simp] lemma preimage_indep_iff {β : Type*} {M : matroid β} {f : α → β} {I : set α} : 
    (M.preimage f).indep I ↔ M.indep (f '' I) ∧ inj_on f I :=
by simp [preimage]

end preimage

section single_extensions

def add_loop (M : matroid α) (f : α) : matroid α := M.restrict' (insert f M.E)

@[simp] lemma add_loop_ground (M : matroid α) (f : α) : (M.add_loop f).E = insert f M.E := rfl

@[simp] lemma add_loop_indep_iff {f : α} : (M.add_loop f).indep I ↔ M.indep I := 
begin
  rw [add_loop, restrict'_indep_iff, and_iff_left_iff_imp],
  exact fun hI, hI.subset_ground.trans (subset_insert _ _), 
end 

lemma eq_add_loop_iff {f : α} (M M' : matroid α) (hf : f ∉ M.E) : 
    M' = add_loop M f ↔ M'.loop f ∧ M' ⟍ f = M :=
begin
  rw [loop_iff_dep, dep_iff, singleton_subset_iff], 
  split, 
  { rintro rfl, 
    rw [add_loop_indep_iff, add_loop_ground, and_iff_left (mem_insert _ _), indep_singleton, 
      and_iff_right (show ¬M.nonloop f, from fun h, hf h.mem_ground), 
      eq_iff_indep_iff_indep_forall, delete_elem, delete_ground, add_loop_ground], 
    simp only [insert_diff_of_mem, mem_singleton, sdiff_eq_left, disjoint_singleton_right,  
      delete_indep_iff, add_loop_indep_iff, and_iff_left_iff_imp, and_iff_right hf],
    rintro I hI - hfI,
    exact (hI hfI).2 rfl },
  rintro ⟨hfl,rfl⟩,  
  apply eq_of_indep_iff_indep_forall _ (fun I hI, _), 
  { simp only [delete_elem, add_loop_ground, delete_ground, insert_diff_singleton],
    rw [insert_eq_of_mem hfl.2] },
  simp only [delete_elem, add_loop_indep_iff, delete_indep_iff, disjoint_singleton_right, 
    iff_self_and], 
  exact fun hI' hfI, hfl.1 (hI'.subset (singleton_subset_iff.2 hfI)), 
end 

def add_coloop (M : matroid α) (f : α) : matroid α := (M﹡.add_loop f)﹡  

lemma add_coloop_eq {f : α} (M M' : matroid α) (hf : f ∉ M.E) : 
    M' = add_coloop M f ↔ M'.coloop f ∧ M' ⟍ f = M := 
begin
  rw [add_coloop, eq_dual_comm, eq_comm, eq_add_loop_iff _ _ (show f ∉ M﹡.E, from hf), 
    dual_loop_iff_coloop, eq_dual_comm, delete_elem, dual_delete_dual_eq_contract, 
    delete_elem, and.congr_right_iff, eq_comm], 
  intro hf', 
  rw [contract_eq_delete_of_subset_coloops], 
  rwa [singleton_subset_iff, ← coloop_iff_mem_cl_empty ], 
end 

lemma add_coloop_del_eq {f : α} (M : matroid α) (hf : f ∉ M.E) : add_coloop M f ⟍ f = M := 
  (((M.add_coloop_eq _) hf).1 rfl).2

@[simp] lemma add_coloop_ground (M : matroid α) (f : α) : (M.add_coloop f).E = insert f M.E := rfl

variables {e f : α} [decidable_eq α]

/-- extend `e` in `M` by a parallel element `f`. -/
def parallel_extend (M : matroid α) (e f : α) : matroid α := M.preimage ((@id α).update f e)

lemma parallel_extend_ground (he : e ∈ M.E) (f : α) : (M.parallel_extend e f).E = insert f M.E :=
begin
  simp only [parallel_extend, matroid.preimage_ground_eq], 
  refine subset_antisymm _ (insert_subset.2 ⟨by simpa, fun x hx, _⟩), 
  { rintro x hx, 
    simp only [set.mem_preimage] at hx,
    obtain (rfl | hx') := eq_or_ne x f, 
    { exact mem_insert _ _ },
    rw [function.update_apply, if_neg hx'] at hx, 
    exact or.inr hx },
  obtain (rfl | hx') := eq_or_ne x f,
  { simpa },
  rwa [mem_preimage, function.update_apply, if_neg hx'], 
end 

/-- If `e ∉ M.E`, then `M.parallel_extend e f` has the junk value `M ⟍ f`. -/
lemma parallel_extend_not_mem (he : e ∉ M.E) (f : α) : M.parallel_extend e f = M ⟍ f := 
begin
  classical, 
  simp_rw [eq_iff_indep_iff_indep_forall, parallel_extend, preimage_ground_eq, 
    preimage_update function.injective_id, if_neg he, preimage_id, preimage_indep_iff, image_update, 
    image_id, id, delete_elem, delete_indep_iff, delete_ground, and_iff_right rfl, subset_diff, 
    disjoint_singleton_right, update_id_inj_on_iff], 
  rintro I ⟨hI, hfI⟩, 
  simp [if_neg hfI, hfI], 
end 

lemma parallel_extend_delete_eq (M : matroid α) (e f : α) (hf : f ∉ M.E) : 
    (M.parallel_extend e f) ⟍ f = M := 
begin
  classical,
  obtain (he | he) := em' (e ∈ M.E), 
  { rwa [parallel_extend_not_mem he, delete_elem, delete_elem, delete_delete, union_singleton, 
      pair_eq_singleton, delete_eq_self_iff, disjoint_singleton_left],  },
  simp_rw [delete_elem, eq_iff_indep_iff_indep_forall, delete_ground, parallel_extend_ground he, 
    delete_indep_iff, subset_diff, disjoint_singleton_right, insert_diff_self_of_not_mem hf, 
    and_iff_right rfl, parallel_extend, preimage_indep_iff, image_update, 
    update_inj_on_iff, and_iff_right (function.injective_id.inj_on _)], 
  rintro I ⟨hIs, hfI⟩,  
  simp [if_neg hfI, hfI], 
end

lemma parallel_extend_indep_iff (he : M.nonloop e) (hf : f ∉ M.E) {I : set α} : 
    (M.parallel_extend e f).indep I ↔ 
      (f ∉ I ∧ M.indep I) ∨ (f ∈ I ∧ e ∉ I ∧ M.indep (insert e (I \ {f}))) := 
begin
  classical,
  rw [parallel_extend, preimage_indep_iff, update_inj_on_iff, 
    and_iff_right (function.injective_id.inj_on _), image_update, image_id, image_id], 
  split_ifs, 
  { rw [and_iff_right h, iff_true_intro h, true_implies_iff, not_true, false_and, false_or, 
      and_comm, and.congr_left_iff],  
    refine fun h, ⟨fun h' heI, hf _, fun h' x hxI, _⟩, 
    { rw [← h' _ heI rfl], exact he.mem_ground },
    rintro rfl, 
    exact (h' hxI).elim },
  rw [iff_false_intro h, false_implies_iff, and_true, ← not_true, not_not, true_and, not_true, 
    false_and, or_false], 
end 

lemma parallel_extend_circuit (he : M.nonloop e) (hf : f ∉ M.E) : 
    (M.parallel_extend e f).circuit {e,f} :=
begin
  simp_rw [circuit_iff_dep_forall_diff_singleton_indep, dep_iff, 
    parallel_extend_ground he.mem_ground, insert_subset, 
    and_iff_right (mem_insert_of_mem _ he.mem_ground), 
    and_iff_left (singleton_subset_iff.2 (mem_insert _ _)), mem_insert_iff, mem_singleton_iff, 
    parallel_extend_indep_iff he hf], 
  simp only [mem_insert_iff, or_true, not_true, false_and, eq_self_iff_true, mem_singleton_iff, 
  true_or, not_false_iff, mem_diff, true_and, not_not, forall_eq_or_imp, insert_diff_of_mem, 
  sdiff_sdiff_self, bot_eq_empty, insert_emptyc_eq, indep_singleton, forall_eq, or_false, he, 
    and_true],
  obtain (rfl | hne) := eq_or_ne e f, 
  { simp }, 
  simp only [hne.symm, false_and, not_false_iff, false_or, true_and], 
  rwa [← insert_diff_singleton_comm hne, diff_self, insert_emptyc_eq, indep_singleton], 
end 

lemma eq_parallel_extend_iff {M M' : matroid α} (he : M.nonloop e) (hf : f ∉ M.E) : 
    M' = M.parallel_extend e f ↔ M'.circuit {e,f} ∧ M' ⟍ f = M := 
begin
  split, 
  { rintro rfl, 
    exact ⟨parallel_extend_circuit he hf, M.parallel_extend_delete_eq e f hf⟩ },
  rintro ⟨hC, rfl⟩, 
  have hef := pair_subset_iff.1 hC.subset_ground, 
  have hne : e ≠ f := by {rintro rfl, exact hf he.mem_ground},  
  have heE : e ∈ (M' ⟍ f).E, 
  { rw [delete_elem, delete_ground, mem_diff], exact ⟨hef.1, hne⟩ },
  rw [eq_iff_indep_iff_indep_forall, parallel_extend_ground heE, delete_elem, delete_ground, 
    insert_diff_singleton, eq_comm, insert_eq_self, and_iff_right hef.2], swap, 
  
  simp_rw [←delete_elem, parallel_extend_indep_iff he hf, delete_elem, delete_indep_iff, 
    disjoint_singleton_right], 
  simp only [mem_insert_iff, not_mem_diff_singleton, or_false, 
    and_iff_left (show ¬ (f = e) , from hne.symm)], 
  refine fun I hI, _, 
  obtain (hfI | hfI) := em (f ∈ I), 
  { simp only [hfI, not_true, and_false, true_and, false_or],
    refine ⟨λ h, ⟨fun heI, _, _⟩, λ h, _⟩,
    { exact hC.dep.not_indep (h.subset (pair_subset_iff.2 ⟨heI, hfI⟩)) },
    { rw [indep_iff_forall_subset_not_circuit', insert_subset, and_iff_right hef.1, 
        and_iff_left ((diff_subset _ _).trans hI)],
      rintro C' hC'ss hC', 
      have hCne : C' ≠ {e,f},
      { rintro rfl, obtain (rfl | h') := hC'ss (or.inr rfl), exact hne rfl, exact h'.2 rfl }, 
      obtain ⟨C₀, hC₀ss, hC₀⟩ := hC'.elimination hC hCne e, 
      refine hC₀.dep.not_indep (h.subset (hC₀ss.trans _)), 
      rw [diff_subset_iff, union_subset_iff, insert_subset, 
        and_iff_right (show e ∈ {e} ∪ I, from or.inl rfl), singleton_subset_iff, 
        and_iff_left (show f ∈ {e} ∪ I, from or.inr hfI), singleton_union] , 
      exact hC'ss.trans (insert_subset_insert (diff_subset _ _)) },
    rw [indep_iff_forall_subset_not_circuit], 
    rintro C' hC'ss hC', 
    have hCne : C' ≠ {e,f},
    { rintro rfl, exact h.1 (pair_subset_iff.1 hC'ss).1, },
    obtain ⟨C₀, hC₀ss, hC₀⟩ := hC'.elimination hC hCne f, 
    rw [union_insert, union_singleton, insert_comm, insert_diff_of_mem _ (by simp : f ∈ {f})] 
      at hC₀ss, 
    
    refine hC₀.dep.not_indep (h.2.subset (hC₀ss.trans _)), 
    rw [insert_diff_singleton_comm hne], 
    exact (diff_subset_diff_left (insert_subset_insert hC'ss)) },
  simp [hfI], 
end 

/-- extend `e` in `M` by an element `f` in series. -/
def series_extend (M : matroid α) (e f : α) : matroid α := (M﹡.parallel_extend e f)﹡ 

lemma series_extend_ground (he : e ∈ M.E) : (M.series_extend e f).E = insert f M.E :=
by simp [series_extend, parallel_extend_ground (show e ∈ M﹡.E, from he)]

lemma series_extend_contract_eq (M : matroid α) (e f : α) (hf : f ∉ M.E) : 
  (M.series_extend e f) ⟋ f = M := 
dual_inj 
  (by rwa [series_extend, contract_elem, dual_contract_dual_eq_delete, ← delete_elem, 
    parallel_extend_delete_eq ])

lemma series_extend_cocircuit (heE : e ∈ M.E) (he : ¬ M.coloop e) (hf : f ∉ M.E) : 
  (M.series_extend e f).cocircuit {e,f} :=
begin
  have hnl : M﹡.nonloop e,
  { rw [nonloop, dual_loop_iff_coloop], exact ⟨he, heE⟩ },
  rw [←dual_circuit_iff_cocircuit ],
  convert parallel_extend_circuit hnl hf, 
  rw [eq_comm, eq_dual_comm], 
  refl, 
end

lemma eq_series_extend_iff {M M' : matroid α} (heE : e ∈ M.E) (he : ¬M.coloop e) (hf : f ∉ M.E) : 
  M' = M.series_extend e f ↔ M'.cocircuit {e,f} ∧ M' ⟋ f = M := 
begin
  have hnl : M﹡.nonloop e,
  { rw [nonloop, dual_loop_iff_coloop], exact ⟨he, heE⟩ },
  rw [series_extend, ← dual_circuit_iff_cocircuit, ← dual_inj_iff, dual_dual, 
    eq_parallel_extend_iff hnl (show f ∉ M﹡.E, from hf), eq_dual_comm, delete_elem, 
    dual_delete_dual_eq_contract, ← contract_elem, eq_comm], 
end 

end single_extensions


section unif

/-- Given `I ⊆ E`, the matroid on `E` whose unique base is the set `I`. 
  (If `I` is not a subset of `E`, the base is `I ∩ E` )-/
def trivial_on (I E : set α) : matroid α := 
matroid_of_base E (λ X, X = I ∩ E) ⟨_, rfl⟩ 
(by { rintro B₁ B₂ rfl rfl x h, simpa using h })
(begin 
  rintro Y - J ⟨B, rfl, hJB⟩ hJY, 
  use I ∩ Y ∩ E,
  simp only [mem_maximals_set_of_iff, exists_eq_left, subset_inter_iff, inter_subset_right, 
    and_true, and_imp], 
  rw [inter_right_comm, and_iff_left (inter_subset_right _ _), inter_assoc, 
    and_iff_right (inter_subset_left _ _), and_iff_left hJY, 
    and_iff_right (subset_inter_iff.mp hJB)], 
  exact λ X hXI hXE hJX hXY hss, hss.antisymm (subset_inter hXI (subset_inter hXE hXY)), 
end)
(by { rintro B rfl, apply inter_subset_right })

lemma trivial_on_base_iff (hIE : I ⊆ E) : (trivial_on I E).base B ↔ B = I := 
by simp only [trivial_on, matroid_of_base_apply, inter_eq_self_of_subset_left hIE]

lemma trivial_on_indep_iff (hIE : I ⊆ E) : (trivial_on I E).indep J ↔ J ⊆ I := 
by { simp_rw [indep_iff_subset_base, trivial_on_base_iff hIE], simp }

/-- The truncation of a matroid to finite rank `k`. The independent sets of the truncation
  are the independent sets of the matroid of size at most `k`. -/
def truncate (M : matroid α) (k : ℕ) : matroid α := 
matroid_of_indep_of_bdd' M.E (λ I, M.indep I ∧ I.finite ∧ I.ncard ≤ k) 
(by simp)
(λ I J h hIJ, ⟨h.1.subset hIJ, h.2.1.subset hIJ, (ncard_le_of_subset hIJ h.2.1).trans h.2.2⟩ )
(begin
  rintro I J ⟨hI, hIfin, hIc⟩ ⟨hJ, hJfin, hJc⟩ hIJ, 
  obtain ⟨e, heJ, heI, hi⟩ := hI.augment_of_finite hJ hIfin hIJ, 
  refine ⟨e, heJ, heI, hi, hIfin.insert e, (ncard_insert_le _ _).trans _⟩, 
  rw [nat.add_one_le_iff], 
  exact hIJ.trans_le hJc, 
end) 
(⟨k, λ I, and.right⟩)
(λ I hI, hI.1.subset_ground)

@[simp] lemma truncate_indep_iff : (M.truncate k).indep I ↔ (M.indep I ∧ I.finite ∧ I.ncard ≤ k) := 
by simp [truncate]

lemma truncate_base_iff [finite_rk M] (h : k ≤ M.rk) :
  (M.truncate k).base B ↔ M.indep B ∧ B.ncard = k :=
begin
  simp_rw [base_iff_maximal_indep, truncate_indep_iff, and_imp], 
  split, 
  { rintro ⟨⟨hBi, hBin, hBc⟩, hBmax⟩, 
    refine ⟨hBi, hBc.antisymm _⟩, 
    obtain ⟨B', hB', hBB'⟩ := hBi.exists_base_supset, 
    rw ←hB'.card at h, 
    obtain ⟨J, hBJ, hJB', rfl⟩ := exists_intermediate_set' hBc h hBB', 
    rw hBmax J (hB'.indep.subset hJB') (hB'.finite.subset hJB') rfl.le hBJ },
  rintro ⟨hB, rfl⟩, 
  exact ⟨⟨hB, hB.finite, rfl.le⟩, λ I hI hIfin hIc hBI, eq_of_subset_of_ncard_le hBI hIc hIfin⟩, 
end 

/-- The matroid on `E` whose only basis is `E` -/
def free_on (E : set α) : matroid α := trivial_on E E

@[simp] lemma free_on_base_iff (E : set α) : (free_on E).base B ↔ B = E := 
by rw [free_on, trivial_on_base_iff subset.rfl]

@[simp] lemma free_on_indep_iff (E : set α) : (free_on E).indep I ↔ I ⊆ E := 
by rw [free_on, trivial_on_indep_iff subset.rfl]

@[simp] lemma free_on_rk_eq (E : set α) : (free_on E).rk = E.ncard :=
by { obtain ⟨B, hB⟩ := (free_on E).exists_base, rw [←hB.card, (free_on_base_iff _).mp hB] }

/-- A uniform matroid with a given rank and ground set -/
def set.unif_on (E : set α) (k : ℕ) := (free_on E).truncate k 

@[simp] lemma set.unif_on_ground_eq : (E.unif_on k).E = E := rfl 

@[simp] lemma set.unif_on_indep_iff : (E.unif_on k).indep I ↔ I.finite ∧ I.ncard ≤ k ∧ I ⊆ E :=
by {simp [set.unif_on, and_comm (I ⊆ E), and_assoc], }

lemma set.unif_on_indep_iff' : (E.unif_on k).indep I ↔ I.encard ≤ k ∧ I ⊆ E := 
by rw [encard_le_coe_iff, set.unif_on_indep_iff, and_assoc]

lemma set.eq_unif_on_iff : M = E.unif_on a ↔ M.E = E ∧ ∀ I, M.indep I ↔ I.encard ≤ a ∧ I ⊆ E := 
begin
  simp_rw [eq_iff_indep_iff_indep_forall, set.unif_on_ground_eq, set.unif_on_indep_iff', 
    and.congr_right_iff],  
  rintro rfl, 
  exact ⟨λ h I, ⟨λ hI, (h I hI.subset_ground).mp hI, λ hI, (h I hI.2).mpr hI⟩, 
    λ h I hIE, h I⟩,
end 

/-- A uniform matroid of a given rank whose ground set is the universe of a type -/
def unif_on (α : Type*) (k : ℕ) := (univ : set α).unif_on k 

@[simp] lemma unif_on_indep_iff [_root_.finite α] : (unif_on α k).indep I ↔ I.ncard ≤ k := 
by simp only [unif_on, set.unif_on_indep_iff, subset_univ, and_true, and_iff_right_iff_imp, 
    iff_true_intro (to_finite I), imp_true_iff]

/-- A canonical uniform matroid, with rank `a` and ground type `fin b`. -/
def unif (a b : ℕ) := unif_on (fin b) a 

@[simp] lemma unif_ground_eq (a b : ℕ) : (unif a b).E = univ := rfl 

@[simp] lemma unif_indep_iff (I : set (fin b)) : (unif a b).indep I ↔ I.ncard ≤ a :=
by rw [unif, unif_on_indep_iff]

@[simp] lemma unif_indep_iff' (I : set (fin b)) : (unif a b).indep I ↔ I.encard ≤ a :=
by rw [unif_indep_iff, encard_le_coe_iff, and_iff_right (to_finite I)]

@[simp] lemma unif_base_iff (hab : a ≤ b) {B : set (fin b)} : 
  (unif a b).base B ↔ B.ncard = a := 
begin
  simp only [unif, unif_on, set.unif_on], 
  rw [truncate_base_iff, free_on_indep_iff, and_iff_right (subset_univ _)], 
  rwa [free_on_rk_eq, ncard_eq_to_finset_card, finite.to_finset_univ, finset.card_fin], 
end 

lemma iso_unif_iff {a b : ℕ} {M : matroid α} : 
  nonempty (M ≃i (unif a b)) ↔ (M = M.E.unif_on a ∧ M.E.encard = (b : ℕ∞)) := 
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨i⟩ := h,
    set e := i.to_equiv, 
    rw [encard, part_enat.card_congr e, unif_ground_eq, part_enat.card_eq_coe_fintype_card, 
      part_enat.with_top_equiv_coe, nat.cast_inj, ←set.to_finset_card, to_finset_univ, 
      finset.card_fin, eq_self_iff_true, and_true, eq_iff_indep_iff_indep_forall, 
      set.unif_on_ground_eq, and_iff_right rfl], 
    intros I hI, 
    rw [set.unif_on_indep_iff, and_iff_left hI, ←encard_le_coe_iff, i.on_indep hI, unif_indep_iff', 
      iso.image, encard_image_of_injective _ (subtype.coe_injective), 
      encard_image_of_injective _ (equiv_like.injective i), 
      encard_preimage_of_injective_subset_range subtype.coe_injective], 
    rwa subtype.range_coe },
  rw [encard_eq_coe_iff, ncard] at h, 
  obtain ⟨h1, hfin, h'⟩ := h, 
  haveI := finite_coe_iff.mpr hfin, 
  set e := (finite.equiv_fin_of_card_eq h').trans (equiv.set.univ (fin b)).symm, 
  refine ⟨@iso_of_indep _ _ M (unif a b) e (λ I, _)⟩,  
  apply_fun indep at h1, 
  rw [h1, set.unif_on_indep_iff'],  
  simp only [image_subset_iff, subtype.coe_preimage_self, subset_univ, and_true, equiv.coe_trans, 
    function.comp_app, equiv.set.univ_symm_apply, unif_indep_iff', 
    encard_image_of_injective _ subtype.coe_injective],
  rw [encard_image_of_injective], 
  intros x y, 
  simp,  
end 

/-- Horrible proof. Should be improved using `simple` api -/
lemma iso_line_iff {k : ℕ} (hk : 2 ≤ k) : 
  nonempty (M ≃i (unif 2 k)) ↔ 
    (∀ e f ∈ M.E, M.indep {e,f}) ∧ M.rk = 2 ∧ M.E.finite ∧ M.E.ncard = k :=
begin
  simp_rw [iso_unif_iff, encard_eq_coe_iff, ← and_assoc, and.congr_left_iff, 
    set.eq_unif_on_iff, and_iff_right rfl, nat.cast_bit0, enat.coe_one], 
  rintro rfl hfin, 
  have lem : ∀ x y, ({x,y} : set α).encard ≤ 2, 
  { intros x y, 
    rw [(({x,y} : set α).to_finite.encard_eq), ←nat.cast_two, nat.cast_le],   
    exact (ncard_insert_le _ _).trans (by simp) },
  haveI : M.finite := ⟨hfin⟩, 
  refine ⟨λ h, ⟨λ e he f hf, (h _).mpr ⟨lem _ _,_⟩,_⟩, λ h I, _⟩,
  
  { rintro x ((rfl : x = e)| (rfl : x = f)); assumption  },
  { rw [rk],
    rw [←one_add_one_eq_two, nat.add_one_le_iff, one_lt_ncard_iff hfin] at hk, 
    obtain ⟨a, b, ha, hb, hne⟩ := hk, 
    have hss : {a,b} ⊆ M.E, by {rintro x ((rfl : x = a) | (rfl : x = b)); assumption}, 
    have hlb := M.r_mono hss, 
    rw [indep.r ((h _).mpr ⟨_, hss⟩), ncard_pair hne] at hlb, 
    { refine hlb.antisymm' _, 
      obtain ⟨B, hB⟩ := M.exists_base, 
      rw [←rk, ←hB.card],
      have h' := ((h B).mp hB.indep).1,
      rw [←nat.cast_two, encard_le_coe_iff] at h', 
      exact h'.2 },
    apply lem },
  rw [←nat.cast_two, encard_le_coe_iff], 
  refine ⟨λ h', ⟨⟨h'.finite, _⟩, h'.subset_ground⟩, _⟩,
  { rw [←h'.r, ←h.2], exact r_le_rk _ _ },
  rintro ⟨⟨hfin, hcard⟩, hss⟩,  
  rw [le_iff_eq_or_lt, nat.lt_iff_add_one_le, ncard_eq_two, ←one_add_one_eq_two, 
    nat.add_le_add_iff_right, ncard_le_one_iff_eq hfin] at hcard, 
  obtain (⟨x,y,-, rfl⟩ | rfl | ⟨e, rfl⟩ ) := hcard, 
  { exact h.1 _ (hss (by simp)) _ (hss (by simp)) }, 
  { simp }, 
  convert h.1 e (hss (by simp)) e (hss (by simp)), 
  simp, 
end 

end unif

end matroid