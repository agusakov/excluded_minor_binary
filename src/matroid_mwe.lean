import .prelim_mwe
import tactic

noncomputable theory
open_locale classical
open_locale big_operators

open set

section prelim -- taken from basic.lean

variables {α : Type*} {I D J B B' B₁ B₂ X Y : set α} {e f : α}

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def exchange_property (P : set α → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

/-- A predicate `P` on sets satisfies the maximal subset property if, for all `X` containing some 
  `I` satisfying `P`, there is a maximal subset of `X` satisfying `P`. -/
def exists_maximal_subset_property (P : set α → Prop) (X : set α) : Prop := 
  ∀ I, P I → I ⊆ X → (maximals (⊆) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty

lemma exists_maximal_subset_property_of_bounded {P : set α → Prop} 
(h : ∃ n, ∀ I, P I → (I.finite ∧ I.ncard ≤ n)) (X : set α): 
  exists_maximal_subset_property P X :=
begin
  obtain ⟨n,h⟩ := h, 
  intros I₀ hI₀ hI₀X,
  set S := {I | P I ∧ I₀ ⊆ I ∧ I ⊆ X} with hS,
  haveI : nonempty S, from ⟨⟨I₀, hI₀, subset.rfl, hI₀X⟩⟩,  
  set f : {I | P I ∧ I₀ ⊆ I ∧ I ⊆ X} → fin (n+1) := 
    λ I, ⟨ncard (I : set α), nat.lt_succ_of_le (h I I.2.1).2⟩ with hf,

  obtain ⟨m, ⟨⟨J,hJ⟩,rfl⟩, hJmax⟩ :=  set.finite.exists_maximal (range f) (range_nonempty _),
  refine ⟨J, hJ, λ K hK hJK, (eq_of_subset_of_ncard_le hJK _ (h _ hK.1).1).symm.subset⟩,
  exact (hJmax _ ⟨⟨K,hK⟩, rfl⟩ (ncard_le_of_subset hJK (h _ hK.1).1)).symm.le,  
end 

private lemma antichain_of_exch {base : set α → Prop} (exch : exchange_property base) 
(hB : base B) (hB' : base B') (h : B ⊆ B') : B = B' :=
begin
  refine h.antisymm (diff_eq_empty.mp (eq_empty_iff_forall_not_mem.mpr (λ x hx, _))), 
  obtain ⟨e,he,-⟩ :=  exch _ _ hB' hB _ hx, 
  exact he.2 (h he.1), 
end 

private lemma diff_aux_of_exch {base : set α → Prop} (exch : exchange_property base) 
(hB₁ : base B₁) (hB₂ : base B₂) (hfin : (B₁ \ B₂).finite) :
(B₂ \ B₁).finite ∧ (B₂ \ B₁).ncard = (B₁ \ B₂).ncard :=
begin
  suffices : ∀ {k B B'}, base B → base B' → (B \ B').finite → ncard (B \ B') = k → 
    (B' \ B).finite ∧ (B' \ B).ncard = k, from this hB₁ hB₂ hfin rfl,  
  intro k, induction k with k IH, 
  { intros B B' hB hB' hfin h0, 
    rw [ncard_eq_zero hfin, diff_eq_empty] at h0, 
    rw [antichain_of_exch exch hB hB' h0, diff_self], 
    simp },
  intros B B' hB hB' hfin hcard, 
  obtain ⟨e,he⟩ := nonempty_of_ncard_ne_zero (by { rw hcard, simp } : (B \ B').ncard ≠ 0), 
  obtain ⟨f,hf,hB0⟩ := exch _ _ hB hB' _ he, 
  have hef : f ≠ e, by { rintro rfl, exact hf.2 he.1 }, 
  
  obtain ⟨hfin',hcard'⟩ := IH hB0 hB' _ _,
  { rw [insert_diff_singleton_comm hef, diff_diff_right, 
      inter_singleton_eq_empty.mpr he.2, union_empty, ←union_singleton, ←diff_diff] at hfin' hcard',
    have hfin'' := hfin'.insert f, 
    rw [insert_diff_singleton, insert_eq_of_mem hf] at hfin'', 
    apply_fun (λ x, x+1) at hcard', 
    rw [ncard_diff_singleton_add_one hf hfin'', ←nat.succ_eq_add_one] at hcard', 
    exact ⟨hfin'', hcard'⟩ },
  { rw [insert_diff_of_mem _ hf.1, diff_diff_comm], 
    exact hfin.diff _ },
  rw [insert_diff_of_mem _ hf.1, diff_diff_comm, ncard_diff_singleton_of_mem he hfin, hcard, 
    nat.succ_sub_one], 
end  

private lemma finite_of_finite_of_exch {base : set α → Prop} (exch : exchange_property base) 
(hB : base B) (hB' : base B') (h : B.finite) : 
  B'.finite :=
begin
  rw [←inter_union_diff B' B], 
  exact finite.union (h.subset (inter_subset_right _ _)) 
    (diff_aux_of_exch exch hB hB' (h.diff _)).1, 
end 

/- an `encard` version -/
private lemma encard_diff_eq_of_exch {base : set α → Prop} (exch : exchange_property base) 
(hB₁ : base B₁) (hB₂ : base B₂) : (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
begin
  obtain (hf | hi) := (B₁ \ B₂).finite_or_infinite, 
  { obtain ⟨hf', he⟩ := diff_aux_of_exch exch hB₁ hB₂ hf, 
    rw [hf.encard_eq, hf'.encard_eq, he] },
  obtain (hf' | hi') := (B₂ \ B₁).finite_or_infinite, 
  { obtain ⟨h, _⟩ := diff_aux_of_exch exch hB₂ hB₁ hf', 
    exact (hi h).elim, },
  rw [hi.encard_eq, hi'.encard_eq], 
end

private lemma encard_eq_of_exch {base : set α → Prop} (exch : exchange_property base)
(hB₁ : base B₁) (hB₂ : base B₂) : B₁.encard = B₂.encard :=
by rw [←encard_diff_add_encard_inter B₁ B₂, encard_diff_eq_of_exch exch hB₁ hB₂, inter_comm, 
    encard_diff_add_encard_inter]

/-- A `matroid` is a nonempty collection of sets satisfying the exchange property and the maximal
  subset property. Each such set is called a `base` of the matroid. -/

@[ext] structure matroid_in (α : Type*) :=
  (ground : set α)
  (base : set α → Prop)
  (exists_base' : ∃ B, base B)
  (base_exchange' : exchange_property base)
  (maximality : ∀ X ⊆ ground, exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B) X)
  (subset_ground' : ∀ B, base B → B ⊆ ground) 

end prelim

namespace matroid_in

section basic -- taken from basic.lean

variables {α : Type*} {I D J B B' B₁ B₂ X Y : set α} {e f : α}

def E (M : matroid_in α) : set α := M.ground

@[simp] lemma ground_eq_E (M : matroid_in α) : M.ground = M.E := rfl 

section tac

@[user_attribute]
meta def ssE_rules : user_attribute :=
{ name := `ssE_rules,
  descr := "lemmas usable to prove subset of ground set" }

@[user_attribute]
meta def ssE_finish_rules : user_attribute :=
{ name := `ssE_finish_rules,
  descr := "finishing lemmas usable to prove subset of ground set" }

meta def ssE_finish : tactic unit := `[solve_by_elim with ssE_finish_rules {max_depth := 2}] 

meta def ssE : tactic unit := `[solve_by_elim with ssE_rules 
  {max_depth := 3, discharger := ssE_finish}]

@[ssE_rules] private lemma inter_right_subset_ground {X Y : set α} {M : matroid_in α} 
(hX : X ⊆ M.E) : X ∩ Y ⊆ M.E := (inter_subset_left _ _).trans hX 

@[ssE_rules] private lemma inter_left_subset_ground {X Y : set α} {M : matroid_in α}
(hX : X ⊆ M.E) : Y ∩ X ⊆ M.E := (inter_subset_right _ _).trans hX 

@[ssE_rules] private lemma diff_subset_ground {X Y : set α} {M : matroid_in α}
(hX : X ⊆ M.E) : X \ Y ⊆ M.E := (diff_subset _ _).trans hX 

@[simp] lemma ground_inter_right {M : matroid_in α} (hXE : X ⊆ M.E . ssE) : M.E ∩ X = X :=
inter_eq_self_of_subset_right hXE  

@[simp] lemma ground_inter_left {M : matroid_in α} (hXE : X ⊆ M.E . ssE) : X ∩ M.E = X :=
inter_eq_self_of_subset_left hXE 

@[ssE_rules] private lemma insert_subset_ground {e : α} {X : set α} {M : matroid_in α} 
(he : e ∈ M.E) (hX : X ⊆ M.E) : insert e X ⊆ M.E := insert_subset.mpr ⟨he, hX⟩

@[ssE_rules] private lemma singleton_subset_ground {e : α} {M : matroid_in α} (he : e ∈ M.E) :
  {e} ⊆ M.E := 
singleton_subset_iff.mpr he

attribute [ssE_rules] mem_of_mem_of_subset empty_subset subset.rfl union_subset

end tac

/-- A set is independent if it is contained in a base.  -/
def indep (M : matroid_in α) (I : set α) : Prop := ∃ B, M.base B ∧ I ⊆ B

/-- A subset of `M.E` is dependent if it is not independent . -/
def dep (M : matroid_in α) (D : set α) : Prop := ¬M.indep D ∧ D ⊆ M.E  

/-- A basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'basis' is used to refer to what we call a 'base'). -/
def basis (M : matroid_in α) (I X : set α) : Prop := 
  I ∈ maximals (⊆) {A | M.indep A ∧ A ⊆ X} ∧ X ⊆ M.E  

/-- A circuit is a minimal dependent set -/
def circuit (M : matroid_in α) (C : set α) : Prop := C ∈ minimals (⊆) {X | M.dep X}

/-- A coindependent set is a subset of `M.E` that is disjoint from some base -/
def coindep (M : matroid_in α) (I : set α) : Prop := I ⊆ M.E ∧ (∃ B, M.base B ∧ disjoint I B) 

/-- Typeclass for a matroid having finite ground set. This is just a wrapper for `[M.E.finite]`-/
class finite (M : matroid_in α) : Prop := (ground_finite : M.E.finite)

lemma ground_finite (M : matroid_in α) [M.finite] : M.E.finite := ‹M.finite›.ground_finite 

lemma set_finite (M : matroid_in α) [M.finite] (X : set α) (hX : X ⊆ M.E . ssE) : X.finite :=
M.ground_finite.subset hX 

instance finite_of_finite [@_root_.finite α] {M : matroid_in α} : finite M := 
⟨set.to_finite _⟩ 

class finite_rk (M : matroid_in α) : Prop := (exists_finite_base : ∃ B, M.base B ∧ B.finite) 

variables {M : matroid_in α}

@[ssE_finish_rules] lemma base.subset_ground (hB : M.base B) : B ⊆ M.E :=
M.subset_ground' B hB 

lemma exists_base (M : matroid_in α) : ∃ B, M.base B := M.exists_base'

lemma base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : e ∈ B₁ \ B₂) :
  ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {e}))  :=
M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

lemma base.finite_of_finite (hB : M.base B) (h : B.finite) (hB' : M.base B') : B'.finite :=
finite_of_finite_of_exch M.base_exchange' hB hB' h

lemma base.finite [finite_rk M] (hB : M.base B) : B.finite := 
let ⟨B₀,hB₀⟩ := ‹finite_rk M›.exists_finite_base in hB₀.1.finite_of_finite hB₀.2 hB

lemma base.finite_rk_of_finite (hB : M.base B) (hfin : B.finite) : finite_rk M := ⟨⟨B, hB, hfin⟩⟩ 

lemma base.encard_eq_encard_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : 
  B₁.encard = B₂.encard :=
by rw [encard_eq_of_exch M.base_exchange' hB₁ hB₂]

lemma base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : 
  B₁.ncard = B₂.ncard :=
by rw [←encard_to_nat_eq B₁, hB₁.encard_eq_encard_of_base hB₂, encard_to_nat_eq]

instance finite_rk_of_finite {M : matroid_in α} [finite M] : finite_rk M := 
let ⟨B, hB⟩ := M.exists_base in ⟨⟨B, hB, (M.ground_finite).subset hB.subset_ground⟩⟩ 

@[ssE_finish_rules] lemma indep.subset_ground (hI : M.indep I) : I ⊆ M.E := 
by { obtain ⟨B, hB, hIB⟩ := hI, exact hIB.trans hB.subset_ground } 

lemma base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) :
  B₁ = B₂ :=
antichain_of_exch M.base_exchange' hB₁ hB₂ hB₁B₂

lemma indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B := iff.rfl

lemma dep_iff : M.dep D ↔ ¬M.indep D ∧ D ⊆ M.E := iff.rfl  

@[ssE_finish_rules] lemma dep.subset_ground (hD : M.dep D) : D ⊆ M.E :=
hD.2 

@[ssE_finish_rules] lemma coindep.subset_ground (hX : M.coindep X) : X ⊆ M.E :=
hX.1

lemma indep.not_dep (hI : M.indep I) : ¬ M.dep I := 
λ h, h.1 hI   

lemma dep.not_indep (hD : M.dep D) : ¬ M.indep D := 
hD.1  

lemma dep_of_not_indep (hD : ¬ M.indep D) (hDE : D ⊆ M.E . ssE) : M.dep D := 
⟨hD, hDE⟩ 

lemma indep_of_not_dep (hI : ¬ M.dep I) (hIE : I ⊆ M.E . ssE) : M.indep I := 
by_contra (λ h, hI ⟨h, hIE⟩)

@[simp] lemma not_dep_iff (hX : X ⊆ M.E . ssE) : ¬ M.dep X ↔ M.indep X := 
by rw [dep, and_iff_left hX, not_not]

@[simp] lemma not_indep_iff (hX : X ⊆ M.E . ssE) : ¬ M.indep X ↔ M.dep X := 
by rw [dep, and_iff_left hX] 

lemma indep.exists_base_supset (hI : M.indep I) : ∃ B, M.base B ∧ I ⊆ B :=
hI

lemma indep.subset (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma dep.supset (hD : M.dep D) (hDX : D ⊆ X) (hXE : X ⊆ M.E . ssE) : M.dep X := 
dep_of_not_indep (λ hI, (hI.subset hDX).not_dep hD)

@[simp] lemma empty_indep (M : matroid_in α) : M.indep ∅ :=
exists.elim M.exists_base (λ B hB, ⟨_, hB, B.empty_subset⟩)

lemma indep.finite [finite_rk M] (hI : M.indep I) : I.finite := 
let ⟨B, hB, hIB⟩ := hI in hB.finite.subset hIB  

lemma indep.inter_right (hI : M.indep I) (X : set α) : M.indep (I ∩ X) :=
hI.subset (inter_subset_left _ _)

lemma indep.diff (hI : M.indep I) (X : set α) : M.indep (I \ X) := hI.subset (diff_subset _ _)

lemma base.indep (hB : M.base B) : M.indep B := ⟨B, hB, subset_rfl⟩

lemma base.eq_of_subset_indep (hB : M.base B) (hI : M.indep I) (hBI : B ⊆ I) : B = I :=
let ⟨B', hB', hB'I⟩ := hI in hBI.antisymm (by rwa hB.eq_of_subset_base hB' (hBI.trans hB'I))

lemma base_iff_maximal_indep : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
begin
  refine ⟨λ h, ⟨h.indep, λ _, h.eq_of_subset_indep ⟩,λ h, _⟩,
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h,
  rwa h _ hB'.indep hBB',
end

lemma base_iff_mem_maximals : M.base B ↔ B ∈ maximals (⊆) {I | M.indep I} := 
begin
  rw [base_iff_maximal_indep, maximals], 
  exact ⟨λ h, ⟨h.1,λ I hI hBI, (h.2 I hI hBI).symm.subset⟩,
    λ h, ⟨h.1, λ I hI hBI, hBI.antisymm (h.2 hI hBI)⟩⟩,  
end  

lemma indep.base_of_maximal (hI : M.indep I) (h : ∀ J, M.indep J → I ⊆ J → I = J) : M.base I := 
base_iff_maximal_indep.mpr ⟨hI,h⟩

/-- If the difference of two bases is a singleton, then they differ by an insertion/removal -/
lemma base.eq_exchange_of_diff_eq_singleton (hB : M.base B) (hB' : M.base B') (h : B \ B' = {e}) : 
  ∃ f ∈ B' \ B, B' = (insert f B) \ {e} :=
begin
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e)), 
  have hne : f ≠ e, 
  { rintro rfl, exact hf.2 (h.symm.subset (mem_singleton f)).1 },
  rw insert_diff_singleton_comm hne at hb, 
  refine ⟨f, hf, (hb.eq_of_subset_base hB' _).symm⟩, 
  rw [diff_subset_iff, insert_subset, union_comm, ←diff_subset_iff, h, and_iff_left subset.rfl],
  exact or.inl hf.1,
end  

lemma basis.indep (hI : M.basis I X) : M.indep I := hI.1.1.1

lemma basis.subset (hI : M.basis I X) : I ⊆ X := hI.1.1.2

@[ssE_finish_rules] lemma basis.subset_ground (hI : M.basis I X) : X ⊆ M.E :=
hI.2 

lemma basis.basis_inter_ground (hI : M.basis I X) : M.basis I (X ∩ M.E) := 
by { convert hI, rw [inter_eq_self_of_subset_left hI.subset_ground] }

@[ssE_finish_rules] lemma basis.subset_ground_left (hI : M.basis I X) : I ⊆ M.E := 
hI.indep.subset_ground

lemma basis.eq_of_subset_indep (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
  I = J :=
hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

lemma basis.finite (hI : M.basis I X) [finite_rk M] : I.finite := hI.indep.finite 

lemma basis_iff' : 
  M.basis I X ↔ (M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.E :=
begin
  simp_rw [basis, and.congr_left_iff, maximals, mem_set_of_eq, and_imp, sep_set_of, 
    mem_set_of_eq, and_assoc, and.congr_right_iff],   
  intros hXE hI hIX, 
  exact ⟨λ h J hJ hIJ hJX, hIJ.antisymm (h hJ hJX hIJ), 
    λ h J hJ hIJ hJX, (h J hJ hJX hIJ).symm.subset⟩,
end 

lemma basis_iff (hX : X ⊆ M.E . ssE) : 
  M.basis I X ↔ (M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) :=
by rw [basis_iff', and_iff_left hX]

lemma basis_iff_mem_maximals (hX : X ⊆ M.E . ssE): 
  M.basis I X ↔ I ∈ maximals (⊆) (λ (I : set α), M.indep I ∧ I ⊆ X) :=
begin
  simp_rw [basis_iff, mem_maximals_prop_iff, and_assoc, and_imp, and.congr_right_iff], 
  exact λ hI hIX, ⟨λ h J hJ hJX hIJ, h J hJ hIJ hJX, λ h J hJ hJX hIJ, h hJ hIJ hJX⟩, 
end 

lemma basis.basis_subset (hI : M.basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.basis I Y :=
begin
  rw [basis_iff (hYX.trans hI.subset_ground), and_iff_right hI.indep, and_iff_right hIY], 
  exact λ J hJ hIJ hJY, hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX), 
end 

lemma basis.dep_of_ssubset (hI : M.basis I X) {Y : set α} (hIY : I ⊂ Y) (hYX : Y ⊆ X) : M.dep Y :=
begin
  rw [←not_indep_iff (hYX.trans hI.subset_ground)], 
  exact λ hY, hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX), 
end 

lemma basis.insert_dep (hI : M.basis I X) (he : e ∈ X \ I) : M.dep (insert e I) :=
hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset.mpr ⟨he.1,hI.subset⟩)

lemma basis.mem_of_insert_indep (hI : M.basis I X) (he : e ∈ X) (hIe : M.indep (insert e I)) : 
  e ∈ I :=
by_contra (λ heI, (hI.insert_dep ⟨he, heI⟩).not_indep hIe) 

lemma indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) (hX : X ⊆ M.E . ssE) : 
  ∃ J, M.basis J X ∧ I ⊆ J :=
begin
  obtain ⟨J, ⟨(hJ : M.indep J),hIJ,hJX⟩, hJmax⟩ := M.maximality X hX I hI hIX,
  use J, 
  rw [and_iff_left hIJ, basis_iff, and_iff_right hJ, and_iff_right hJX], 
  exact λ K hK hJK hKX, hJK.antisymm (hJmax ⟨hK, hIJ.trans hJK, hKX⟩ hJK),  
end

lemma exists_basis (M : matroid_in α) (X : set α) (hX : X ⊆ M.E . ssE) : ∃ I, M.basis I X :=
let ⟨I, hI, _⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X) in ⟨_,hI⟩

lemma basis.exists_basis_inter_eq_of_supset (hI : M.basis I X) (hXY : X ⊆ Y) (hY : Y ⊆ M.E . ssE) :
  ∃ J, M.basis J Y ∧ J ∩ X = I :=
begin
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY), 
  refine ⟨J, hJ, subset_antisymm _ (subset_inter hIJ hI.subset)⟩,  
  exact λ e he, hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset.mpr ⟨he.1, hIJ⟩)), 
end   

lemma indep.exists_insert_of_not_base (hI : M.indep I) (hI' : ¬M.base I) (hB : M.base B) : 
  ∃ e ∈ B \ I, M.indep (insert e I) :=
begin
  obtain ⟨B', hB', hIB'⟩ := hI, 
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by { rintro rfl, exact hI' hB' })), 
  obtain (hxB | hxB) := em (x ∈ B), 
  { exact ⟨x, ⟨hxB, hx⟩ , ⟨B', hB', insert_subset.mpr ⟨hxB',hIB'⟩⟩⟩ },
  obtain ⟨e,he, hbase⟩ := hB'.exchange hB ⟨hxB',hxB⟩,    
  exact ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩, 
    ⟨_, hbase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩,  
end  

lemma indep.basis_self (hI : M.indep I) : M.basis I I := 
begin
  rw [basis_iff', and_iff_left hI.subset_ground, and_iff_right hI, and_iff_right subset.rfl], 
  exact λ _ _, subset_antisymm, 
end 

lemma basis.exists_base (hI : M.basis I X) : ∃ B, M.base B ∧ I = B ∩ X :=
begin
  obtain ⟨B,hB, hIB⟩ := hI.indep,
  refine ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩,
  rw hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    (inter_subset_right _ _),
end

lemma base_iff_basis_ground : M.base B ↔ M.basis B M.E :=
begin
  rw [base_iff_maximal_indep, basis_iff, and_congr_right], 
  intro hB, 
  rw [and_iff_right hB.subset_ground], 
  exact ⟨λ h J hJ hBJ hJE, h _ hJ hBJ, λ h I hI hBI, h I hI hBI hI.subset_ground⟩,
end 

lemma base.basis_ground (hB : M.base B) : M.basis B M.E := base_iff_basis_ground.mp hB

lemma indep.basis_of_forall_insert (hI : M.indep I) 
  (hIX : I ⊆ X) (he : ∀ e ∈ X \ I, ¬ M.indep (insert e I)) (hX : X ⊆ M.E . ssE) : M.basis I X :=
begin
  rw [basis_iff, and_iff_right hI, and_iff_right hIX], 
  refine λJ hJ hIJ hJX, hIJ.antisymm (λ e heJ, by_contra (λ heI, he e ⟨hJX heJ, heI⟩ _)),  
  exact hJ.subset (insert_subset.mpr ⟨heJ, hIJ⟩), 
end 

lemma basis.Union_basis_Union {ι : Type*} (X I : ι → set α) (hI : ∀ i, M.basis (I i) (X i)) 
(h_ind : M.indep (⋃ i, I i)) : M.basis (⋃ i, I i) (⋃ i, X i) :=
begin
   
  refine h_ind.basis_of_forall_insert 
    (Union_subset_iff.mpr (λ i, (hI i).subset.trans (subset_Union _ _))) (λ e he hi, _)
    (Union_subset (λ i, (hI i).subset_ground)), 
  simp only [mem_diff, mem_Union, not_exists] at he, 
  obtain ⟨i, heXi⟩ := he.1, 
  exact he.2 i ((hI i).mem_of_insert_indep heXi 
    (hi.subset (insert_subset_insert (subset_Union _ _)))), 
end 

lemma basis.union_basis_union (hIX : M.basis I X) (hJY : M.basis J Y) (h : M.indep (I ∪ J)) : 
  M.basis (I ∪ J) (X ∪ Y) :=
begin 
  rw [union_eq_Union, union_eq_Union], 
  refine basis.Union_basis_Union _ _ _ _,   
  { simp only [bool.forall_bool, bool.cond_ff, bool.cond_tt], exact ⟨hJY, hIX⟩ }, 
  rwa [←union_eq_Union], 
end 

lemma basis.basis_union (hIX : M.basis I X) (hIY : M.basis I Y) : M.basis I (X ∪ Y) :=
by { convert hIX.union_basis_union hIY _; rw union_self, exact hIX.indep }

lemma basis.basis_union_of_subset (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) : 
  M.basis J (J ∪ X) :=
begin
  convert hJ.basis_self.union_basis_union hI (by rwa union_eq_left_iff_subset.mpr hIJ), 
  rw union_eq_left_iff_subset.mpr hIJ, 
end 

lemma basis.insert_basis_insert (hI : M.basis I X) (h : M.indep (insert e I)) : 
  M.basis (insert e I) (insert e X) :=
begin
  convert hI.union_basis_union 
    (indep.basis_self (h.subset (singleton_subset_iff.mpr (mem_insert _ _)))) _, 
  simp, simp, simpa, 
end 

lemma base.base_of_basis_supset (hB : M.base B) (hBX : B ⊆ X) (hIX : M.basis I X) : M.base I :=
begin
  by_contra h, 
  obtain ⟨e,heBI,he⟩ := hIX.indep.exists_insert_of_not_base h hB, 
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he), 
end 

lemma base.basis_of_subset (hX : X ⊆ M.E . ssE) (hB : M.base B) (hBX : B ⊆ X) : M.basis B X :=
begin
  rw [basis_iff, and_iff_right hB.indep, and_iff_right hBX], 
  exact λ J hJ hBJ hJX, hB.eq_of_subset_indep hJ hBJ, 
end 

lemma indep.exists_base_subset_union_base (hI : M.indep I) (hB : M.base B) : 
  ∃ B', M.base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
begin
  obtain ⟨B', hB', hIB'⟩ := hI.subset_basis_of_subset (subset_union_left I B),  
  exact ⟨B', hB.base_of_basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩, 
end 

lemma eq_of_base_iff_base_forall {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E) 
(h : ∀ B ⊆ M₁.E, (M₁.base B ↔ M₂.base B)) : M₁ = M₂ :=
begin
  apply matroid_in.ext _ _ hE, 
  ext B, 
  refine ⟨λ h', (h _ h'.subset_ground).mp h', 
    λ h', (h _ (h'.subset_ground.trans_eq hE.symm)).mpr h'⟩,
end 

lemma eq_of_indep_iff_indep_forall {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E) 
(h : ∀ I ⊆ M₁.E, (M₁.indep I ↔ M₂.indep I)) :
  M₁ = M₂ :=
begin
  refine eq_of_base_iff_base_forall hE (λ B hB, _), 
  rw [base_iff_maximal_indep, base_iff_maximal_indep], 
  split, 
  { rintro ⟨hBi, hmax⟩, 
    rw [←h _ hB, and_iff_right hBi],
    refine λ I hI hBI, hmax I _ hBI, 
    rwa h,  
    rw [hE], 
    exact hI.subset_ground },
  rintro ⟨hBi, hmax⟩, 
  rw [h _ hB, and_iff_right hBi], 
  refine λ I hI hBI,  hmax I _ hBI, 
  rwa ←h, 
  exact hI.subset_ground, 
end

lemma eq_iff_indep_iff_indep_forall {M₁ M₂ : matroid_in α} : 
  M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ I ⊆ M₁.E , M₁.indep I ↔ M₂.indep I :=
⟨λ h, by { subst h, simp }, λ h, eq_of_indep_iff_indep_forall h.1 h.2⟩  

def matroid_of_base {α : Type*} (E : set α) (base : set α → Prop) 
(exists_base : ∃ B, base B) (base_exchange : exchange_property base) 
(maximality : ∀ X ⊆ E, exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B) X)
(support : ∀ B, base B → B ⊆ E) : matroid_in α := 
⟨E, base, exists_base, base_exchange, maximality, support⟩

@[simp] lemma matroid_of_base_apply {α : Type*} (E : set α) (base : set α → Prop) 
(exists_base : ∃ B, base B) (base_exchange : exchange_property base) 
(maximality : ∀ X ⊆ E, exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B) X)
(support : ∀ B, base B → B ⊆ E) :
(matroid_of_base E base exists_base base_exchange maximality support).base = base := rfl 

/-- A version of the independence axioms that avoids cardinality -/
def matroid_of_indep (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_maximal : ∀ X ⊆ E, exists_maximal_subset_property indep X) 
(h_support : ∀ I, indep I → I ⊆ E) : 
  matroid_in α :=
matroid_of_base E (λ B, B ∈ maximals (⊆) indep)
(begin
  obtain ⟨B, ⟨hB,-,-⟩, hB₁⟩ := h_maximal E subset.rfl ∅ h_empty (empty_subset _), 
  exact ⟨B, hB, λ B' hB' hBB', hB₁ ⟨hB',empty_subset _,h_support B' hB'⟩ hBB'⟩, 
end)
(begin
  rintros B B' ⟨hB,hBmax⟩ ⟨hB',hB'max⟩ e he, 
  obtain ⟨f,hf,hfB⟩ :=  h_aug (h_subset hB (diff_subset B {e})) _ ⟨hB',hB'max⟩, 
  simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf, 
  have hfB' : f ∉ B, 
  { intro hfB, have := hf.2 hfB, subst this, exact he.2 hf.1 }, 
  { refine ⟨f, ⟨hf.1, hfB'⟩, by_contra (λ hnot, _)⟩,
    obtain ⟨x,hxB, hind⟩ :=  h_aug hfB hnot ⟨hB, hBmax⟩, 
    simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or_distrib, not_and, not_not] 
      at hxB, 
    have := hxB.2.2 hxB.1, subst this, 
    rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1] at hind, 
    exact not_mem_subset (hBmax hind (subset_insert _ _)) hfB' (mem_insert _ _) },
  simp only [maximals, mem_sep_iff, diff_singleton_subset_iff, not_and, not_forall, exists_prop],
  exact λ _, ⟨B, hB, subset_insert _ _, λ hss, (hss he.1).2 rfl⟩, 
end)
(begin
  rintro X hXE I ⟨B, hB, hIB⟩ hIX, 
  -- rintro I X ⟨B, hB,  hIB⟩ hIX, 
  obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal X hXE I (h_subset hB.1 hIB) hIX, 
  obtain ⟨BJ, hBJ⟩ := h_maximal E subset.rfl J hJ (h_support J hJ), 
  refine ⟨J, ⟨⟨BJ,_, hBJ.1.2.1⟩ ,hIJ,hJX⟩, _⟩,  
  { exact ⟨hBJ.1.1, λ B' hB' hBJB', hBJ.2 ⟨hB',hBJ.1.2.1.trans hBJB', h_support B' hB'⟩ hBJB'⟩ },
  simp only [mem_set_of_eq, and_imp, forall_exists_index], 
  rintro A B' ⟨(hB'i : indep _), hB'max⟩ hB'' hIA hAX hJA, 
  exact hJmax ⟨h_subset hB'i hB'', hIA, hAX⟩ hJA,
end )
(λ B hB, h_support B hB.1)

@[simp] lemma matroid_of_indep_apply (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_maximal : ∀ X ⊆ E, exists_maximal_subset_property indep X) 
(h_support : ∀ I, indep I → I ⊆ E)  : 
(matroid_of_indep E indep h_empty h_subset h_aug h_maximal h_support).indep = indep :=
begin
  ext I, 
  simp only [matroid_in.indep, matroid_of_indep], 
  refine ⟨λ ⟨B, hB, hIB⟩, h_subset hB.1 hIB, λ hI, _⟩, 
  obtain ⟨B, ⟨hB, hIB, -⟩, hBmax⟩ :=  h_maximal E subset.rfl I hI (h_support _ hI), 
  exact ⟨B, ⟨hB, λ B' hB' hBB', hBmax ⟨hB', hIB.trans hBB', h_support _ hB'⟩ hBB'⟩, hIB⟩, 
end 

/-- If there is an absolute upper bound on the size of an independent set, then the maximality 
  axiom isn't needed to define a matroid by independent sets. -/
def matroid_of_indep_of_bdd (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_bdd : ∃ n, ∀ I, indep I → I.finite ∧ I.ncard ≤ n )
(h_support : ∀ I, indep I → I ⊆ E) : matroid_in α :=
matroid_of_indep E indep h_empty h_subset h_aug 
  (λ X h, exists_maximal_subset_property_of_bounded h_bdd X) 
  h_support 

@[simp] lemma matroid_of_indep_of_bdd_apply (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_bdd : ∃ n, ∀ I, indep I → I.finite ∧ I.ncard ≤ n ) 
(h_support : ∀ I, indep I → I ⊆ E) : 
(matroid_of_indep_of_bdd E indep h_empty h_subset h_aug h_bdd h_support).indep = indep := 
by simp [matroid_of_indep_of_bdd]

instance (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I)) (h_bdd : ∃ n, ∀ I, indep I → I.finite ∧ I.ncard ≤ n ) 
(h_support : ∀ I, indep I → I ⊆ E) : 
matroid_in.finite_rk (matroid_of_indep_of_bdd E indep h_empty h_subset h_aug h_bdd h_support) := 
begin
  obtain ⟨B, hB⟩ := 
    (matroid_of_indep_of_bdd E indep h_empty h_subset h_aug h_bdd h_support).exists_base, 
  obtain ⟨h, h_bdd⟩ := h_bdd,  
  refine hB.finite_rk_of_finite (h_bdd B _).1,
  rw [←matroid_of_indep_of_bdd_apply E indep, matroid_in.indep], 
  exact ⟨_, hB, subset.rfl⟩,  
end 

def matroid_of_indep_of_bdd' (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard →
  ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) (h_bdd : ∃ n, ∀ I, indep I → I.finite ∧ I.ncard ≤ n )
(h_support : ∀ I, indep I → I ⊆ E) : matroid_in α :=
matroid_of_indep_of_bdd E indep h_empty h_subset 
(begin
  intros I J hI hIn hJ, 
  by_contra' h', 
  obtain (hlt | hle) := lt_or_le I.ncard J.ncard, 
  { obtain ⟨e,heJ,heI, hi⟩ :=  ind_aug hI hJ.1 hlt, 
    exact h' e ⟨heJ,heI⟩ hi },
  obtain (h_eq | hlt) := hle.eq_or_lt, 
  { refine hIn ⟨hI, λ K (hK : indep K) hIK, hIK.ssubset_or_eq.elim (λ hss, _) 
      (λ h, h.symm.subset)⟩,
    obtain ⟨f, hfK, hfJ, hi⟩ := ind_aug hJ.1 hK (h_eq.trans_lt (ncard_lt_ncard hss _)), 
    { exact (hfJ (hJ.2 hi (subset_insert _ _) (mem_insert f _))).elim },
    obtain ⟨n, hn⟩ := h_bdd, 
    exact (hn K hK).1 },
  obtain ⟨e,heI, heJ, hi⟩ := ind_aug hJ.1 hI hlt, 
    exact heJ (hJ.2 hi (subset_insert _ _) (mem_insert e _)), 
end) h_bdd h_support 

@[simp] lemma matroid_of_indep_of_bdd'_apply (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard →
  ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) (h_bdd : ∃ n, ∀ I, indep I → I.finite ∧ I.ncard ≤ n )
(h_support : ∀ I, indep I → I ⊆ E) : 
(matroid_of_indep_of_bdd' E indep h_empty h_subset ind_aug h_bdd h_support).indep = indep :=
by simp [matroid_of_indep_of_bdd']

lemma base_compl_iff_mem_maximals_disjoint_base' (hB : B ⊆ M.E . ssE) : 
  M.base (M.E \ B) ↔ B ∈ maximals (⊆) {I | I ⊆ M.E ∧ ∃ B, M.base B ∧ disjoint I B} := 
begin
  refine ⟨λ h, ⟨⟨hB,_,h,disjoint_sdiff_right⟩,_⟩, λ h, _⟩, 
  { rintro X ⟨hXE,B', hB', hXB'⟩ hBX,
    rw [hB'.eq_of_subset_base h (subset_diff.mpr ⟨hB'.subset_ground,_⟩), 
      ←subset_compl_iff_disjoint_right, diff_eq, compl_inter, compl_compl] at hXB', 
    { refine (subset_inter hXE hXB').trans _, 
      rw [inter_distrib_left, inter_compl_self, empty_union],
      exact inter_subset_right _ _ },
    exact (disjoint_of_subset_left hBX hXB').symm },
  obtain ⟨⟨-, B', hB', hIB'⟩, h⟩ := h, 
  suffices : B' = M.E \ B, rwa ←this, 
  rw [subset_antisymm_iff, subset_diff, disjoint.comm, and_iff_left hIB', 
    and_iff_right hB'.subset_ground, diff_subset_iff], 

  intros e he, 
  rw [mem_union, or_iff_not_imp_right], 
  intros heB', 
  refine h ⟨insert_subset.mpr ⟨he, hB⟩, ⟨B', hB', _⟩⟩ 
    (subset_insert _ _) (mem_insert e B), 
  rw [←union_singleton, disjoint_union_left, disjoint_singleton_left], 
  exact ⟨hIB', heB'⟩, 
end 

def dual (M : matroid_in α) : matroid_in α := 
matroid_of_indep M.E (λ I, I ⊆ M.E ∧ ∃ B, M.base B ∧ disjoint I B) 
⟨empty_subset M.E, M.exists_base.imp (λ B hB, ⟨hB, empty_disjoint _⟩)⟩ 
(begin
  rintro I J ⟨hJE, B, hB, hJB⟩ hIJ, 
  exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩, 
end) 
(begin
  rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max,  
  have hXE := hX_max.1.1, 
  have hB' := (base_compl_iff_mem_maximals_disjoint_base' hXE).mpr hX_max,
  
  set B' := M.E \ X with hX, 
  have hI := (not_iff_not.mpr (base_compl_iff_mem_maximals_disjoint_base')).mpr hI_not_max, 
  obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB, 
  rw [←compl_subset_compl, ←hIB.sdiff_eq_right, ←union_diff_distrib, diff_eq, compl_inter, 
    compl_compl, union_subset_iff, compl_subset_compl] at hB''₂, 
  
  have hssu := (subset_inter (hB''₂.2) hIE).ssubset_of_ne 
    (by { rintro rfl, apply hI, convert hB'', simp }),
  obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ := exists_of_ssubset hssu, 
  use e, 
  rw [mem_diff, insert_subset, and_iff_left heI, and_iff_right heE, and_iff_right hIE], 
  refine ⟨by_contra (λ heX, heB'' (hB''₁ ⟨_, heI⟩)), ⟨B'', hB'', _⟩⟩, 
  { rw [hX], exact ⟨heE, heX⟩ },
  rw [←union_singleton, disjoint_union_left, disjoint_singleton_left, and_iff_left heB''], 
  exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left,
end) 
(begin
  rintro X hX I' ⟨hI'E, B, hB, hI'B⟩ hI'X, 
  obtain ⟨I, hI⟩ :=  M.exists_basis (M.E \ X) ,
  obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB, 
  refine ⟨(X \ B') ∩ M.E, 
    ⟨_,subset_inter (subset_diff.mpr _) hI'E, (inter_subset_left _ _).trans (diff_subset _ _)⟩, _⟩, 
  { simp only [inter_subset_right, true_and], 
    exact ⟨B', hB', disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left⟩ },
  { rw [and_iff_right hI'X],
    refine disjoint_of_subset_right hB'IB _, 
    rw [disjoint_union_right, and_iff_left hI'B], 
    exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right },
  simp only [mem_set_of_eq, subset_inter_iff, and_imp, forall_exists_index], 
  intros J hJE B'' hB'' hdj hI'J hJX hssJ,
  rw [and_iff_left hJE],  
  rw [diff_eq, inter_right_comm, ←diff_eq, diff_subset_iff] at hssJ, 
  
  have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B',
  { rw [union_subset_iff, and_iff_left (diff_subset _ _),
     ←inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc],
    calc _ ⊆ _ : inter_subset_inter_right _ hssJ 
       ... ⊆ _ : by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty] 
       ... ⊆ _ : inter_subset_right _ _ },
  
  obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB'',
  rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I, 
  
  have : B₁ = B', 
  { refine hB₁.eq_of_subset_indep hB'.indep (λ e he, _), 
    refine (hB₁I he).elim (λ heB'',_) (λ h, h.1), 
    refine (em (e ∈ X)).elim (λ heX, hI' (or.inl ⟨heB'', heX⟩)) (λ heX, hIB' _), 
    refine hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩ 
      (hB₁.indep.subset (insert_subset.mpr ⟨he, _⟩)), 
    refine (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁, 
    refine disjoint_of_subset_left hI.subset disjoint_sdiff_left }, 

  subst this, 

  refine subset_diff.mpr ⟨hJX, by_contra (λ hne, _)⟩, 
  obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne,
  obtain (heB'' | ⟨heB₁,heX⟩ ) := hB₁I heB', 
  { exact hdj.ne_of_mem heJ heB'' rfl },
  exact heX (hJX heJ), 
end) 
(by tauto)

/-- A notation typeclass for matroid duality, denoted by the `﹡` symbol. -/
@[class] structure has_matroid_dual (β : Type*) := (dual : β → β)

postfix `﹡`:(max+1) := has_matroid_dual.dual 

instance matroid_in_dual {α : Type*} : has_matroid_dual (matroid_in α) := ⟨matroid_in.dual⟩

lemma dual_indep_iff_exists' : (M﹡.indep I) ↔ I ⊆ M.E ∧ (∃ B, M.base B ∧ disjoint I B) := 
by simp [has_matroid_dual.dual, dual]

@[simp] lemma dual_ground : M﹡.E = M.E := rfl 

lemma dual_base_iff (hB : B ⊆ M.E . ssE) : M﹡.base B ↔ M.base (M.E \ B) := 
begin
  rw [base_compl_iff_mem_maximals_disjoint_base', base_iff_maximal_indep, dual_indep_iff_exists', 
    mem_maximals_set_of_iff],
  simp [dual_indep_iff_exists'],
end 

lemma dual_base_iff' : M﹡.base B ↔ M.base (M.E \ B) ∧ B ⊆ M.E := 
begin
  obtain (h | h) := em (B ⊆ M.E), 
  { rw [dual_base_iff, and_iff_left h] },
  rw [iff_false_intro h, and_false, iff_false], 
  exact λ h', h h'.subset_ground,  
end  

@[simp] lemma dual_dual (M : matroid_in α) : M﹡﹡ = M := 
begin
  refine eq_of_base_iff_base_forall rfl (λ B hB, _), 
  rw [dual_base_iff, dual_base_iff], 
  rw [dual_ground] at *, 
  simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right], 
end 

lemma dual_indep_iff_coindep : M﹡.indep X ↔ M.coindep X := dual_indep_iff_exists'

lemma base.compl_base_dual (hB : M.base B) : M﹡.base (M.E \ B) := 
by { haveI := fact.mk hB.subset_ground, simpa [dual_base_iff] }

lemma base.compl_inter_basis_of_inter_basis (hB : M.base B) (hBX : M.basis (B ∩ X) X) :
  M﹡.basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := 
begin
  rw basis_iff, 
  refine ⟨(hB.compl_base_dual.indep.subset (inter_subset_left _ _)), inter_subset_right _ _, 
    λ J hJ hBCJ hJX, hBCJ.antisymm (subset_inter _ hJX)⟩, 
  
  obtain ⟨-, B', hB', hJB'⟩ := dual_indep_iff_coindep.mp hJ, 

  obtain ⟨B'', hB'', hsB'', hB''s⟩  := hBX.indep.exists_base_subset_union_base hB', 
  have hB'ss : B' ⊆ B ∪ X, 
  { rw [←diff_subset_diff_iff M.E (by ssE : B ∪ X ⊆ M.E) hB'.subset_ground, subset_diff,
      and_iff_right (diff_subset _ _)],
    rw [diff_inter_diff] at hBCJ, 
    exact disjoint_of_subset_left hBCJ hJB' },
  
  have hB''ss : B'' ⊆ B, 
  { refine λ e he, (hB''s he).elim and.left (λ heB', (hB'ss heB').elim id (λ heX, _)), 
     exact (hBX.mem_of_insert_indep heX (hB''.indep.subset (insert_subset.mpr ⟨he,hsB''⟩))).1 }, 
  
  have := (hB''.eq_of_subset_indep hB.indep hB''ss).symm, subst this,
  rw subset_diff at *, 
  exact ⟨hJX.1, disjoint_of_subset_right hB''s (disjoint_union_right.mpr 
    ⟨disjoint_of_subset_right (inter_subset_right _ _) hJX.2, hJB'⟩)⟩, 
end 

lemma base.inter_basis_iff_compl_inter_basis_dual (hB : M.base B) (hX : X ⊆ M.E . ssE): 
  M.basis (B ∩ X) X ↔ M﹡.basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) :=
begin
  refine ⟨hB.compl_inter_basis_of_inter_basis, λ h, _⟩, 
  simpa using hB.compl_base_dual.compl_inter_basis_of_inter_basis h, 
end 

lemma dual_inj {M₁ M₂ : matroid_in α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
by rw [←dual_dual M₁, h, dual_dual]

@[simp] lemma dual_inj_iff {M₁ M₂ : matroid_in α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

lemma eq_dual_comm {M₁ M₂ : matroid_in α} : M₁ = M₂﹡ ↔ M₂ = M₁﹡ := 
by rw [←dual_inj_iff, dual_dual, eq_comm]

lemma coindep_iff_exists (hX : X ⊆ M.E . ssE) : M.coindep X ↔ ∃ B, M.base B ∧ disjoint X B := 
by rw [coindep, and_iff_right hX]

lemma coindep.exists_disjoint_base (hX : M.coindep X) : ∃ B, M.base B ∧ disjoint X B := hX.2

end basic

section equiv -- taken from equiv.lean

variables {α β α₁ α₂ α₃ : Type*} {M : matroid_in α} {N : matroid_in β} 

structure iso (M₁ : matroid_in α₁) (M₂ : matroid_in α₂) extends equiv M₁.E M₂.E :=
  (on_base' : ∀ (B : set M₁.E), M₁.base (coe '' B) ↔ M₂.base (coe '' (to_fun '' B))) 

infix ` ≃i `:75 := matroid_in.iso 

instance iso.equiv_like {α β : Type*} {M₁ : matroid_in α} {M₂ : matroid_in β} : 
  equiv_like (M₁ ≃i M₂) M₁.E M₂.E := 
{ coe := λ e, e.to_equiv.to_fun,
  inv := λ e, e.to_equiv.inv_fun,
  left_inv := λ e, e.to_equiv.left_inv, 
  right_inv := λ e, e.to_equiv.right_inv,
  coe_injective' := λ e e' h h', by { cases e, cases e', simpa using h }   }

def iso.symm (e : M ≃i N) : N ≃i M := 
{ to_equiv := e.symm, 
  on_base' := begin
    intro B, 
    rw [e.on_base'], 
    congr', 
    exact (e.to_equiv.image_symm_image B).symm, 
  end }

def iso_of_indep (e : M.E ≃ N.E) 
(hi : ∀ (I : set M.E), M.indep (coe '' I) ↔ N.indep (coe '' (e '' I))) : M ≃i N := 
{ to_equiv := e, 
  on_base' := begin
    intro B, 
    simp_rw [base_iff_maximal_indep, equiv.to_fun_as_coe], 
    simp only [image_subset_iff],  
    simp_rw [← hi, and.congr_right_iff],
    refine λ hI, ⟨λ h I hIN hBI, _, λ h I hI hBI, _ ⟩,  
    { have hIE := hIN.subset_ground, 
      rw ←@subtype.range_coe _ N.E at hIE,
      obtain ⟨I, rfl⟩ := subset_range_iff_exists_image_eq.mp hIE, 
      rw [← e.image_preimage I, ← hi] at hIN, 
      have := h _ hIN,
      simp only [subtype.preimage_image_coe, subtype.image_coe_eq_image_coe_iff] at this hBI,
      simp [this hBI] },
    specialize h (coe '' (e '' (coe ⁻¹' I))), 
    simp only [subtype.preimage_image_coe, equiv.preimage_image, subtype.image_coe_eq_image_coe_iff, 
      equiv.image_eq_iff_eq, ← hi, subtype.image_preimage_coe, 
      inter_eq_self_of_subset_left hI.subset_ground] at h, 
    simp only [h hI hBI, subtype.image_preimage_coe, inter_eq_left_iff_subset], 
    exact hI.subset_ground, 
  end }

@[simp] lemma coe_symm (e : M ≃i N) : (e.symm : N.E → M.E) = e.to_equiv.symm := rfl 

def iso.cast {M N : matroid_in α} (h : M = N) : M ≃i N := 
{ to_equiv := equiv.cast (by rw h), 
  on_base' := by { subst h, simp } }

def iso.refl (M : matroid_in α₁) : M ≃i M := 
⟨equiv.refl M.E, by simp⟩ 

def iso.trans {M₁ : matroid_in α₁} {M₂ : matroid_in α₂} {M₃ : matroid_in α₃} 
(e₁ : M₁ ≃i M₂) (e₂ : M₂ ≃i M₃) : M₁ ≃i M₃ :=
{ to_equiv := e₁.to_equiv.trans e₂.to_equiv,
  on_base' := λ B, by { 
    rw [e₁.on_base', e₂.on_base'], 
    convert iff.rfl, 
    rw [← image_comp], 
    refl } }

def iso.image (e : M ≃i N) (B : set α) : set β := coe '' (e '' (coe ⁻¹' B))

def iso.preimage (e : M ≃i N) (B : set β) : set α := coe '' (e ⁻¹' (coe ⁻¹' B))

@[ssE_finish_rules] lemma iso.image_subset_ground (e : M ≃i N) (X : set α) : e.image X ⊆ N.E :=
subtype.coe_image_subset _ _

@[simp] lemma iso.preimage_image (e : M ≃i N) {X : set α} (hX : X ⊆ M.E . ssE) : 
  e.preimage (e.image X) = X :=
begin
  rw ←@subtype.range_coe _ M.E at hX, 
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.mp hX, 
  rw [iso.image, iso.preimage], 
  simp only [subtype.preimage_image_coe, subtype.image_coe_eq_image_coe_iff], 
  exact e.to_equiv.preimage_image X, 
end 

lemma iso.image_eq_preimage_symm (e : M ≃i N) {X : set α} : e.image X = e.symm.preimage X :=
begin
  rw [iso.preimage, coe_symm, iso.image, image_eq_image subtype.coe_injective, 
    ←image_equiv_eq_preimage_symm], refl, 
end 

lemma iso.preimage_eq_image_symm (e : M ≃i N) {X : set β} : e.preimage X = e.symm.image X := 
begin
  rw [iso.image, coe_symm, iso.preimage, image_eq_image subtype.coe_injective, 
    ←preimage_equiv_eq_image_symm], 
  refl, 
end 

lemma iso.image_eq_image_inter_ground (e : M ≃i N) (X : set α) : e.image X = e.image (X ∩ M.E) :=
by rw [iso.image, iso.image, ←preimage_inter_range, subtype.range_coe]

@[simp] lemma iso.image_ground (e : M ≃i N) : e.image M.E = N.E := 
begin
  rw [←@subtype.range_coe _ M.E, ←@subtype.range_coe _ N.E, iso.image], 
  simp only [subtype.range_coe_subtype, set_of_mem_eq, subtype.coe_preimage_self, image_univ],  
  convert image_univ, 
  { exact e.to_equiv.range_eq_univ }, 
  simp, 
end 

lemma iso.image_inter (e : M ≃i N) (X Y : set α) : e.image (X ∩ Y) = e.image X ∩ e.image Y :=
by rw [e.image_eq_image_inter_ground, inter_inter_distrib_right, iso.image, 
    preimage_inter, image_inter (equiv_like.injective e), image_inter subtype.coe_injective, 
    ← iso.image, ←iso.image, ←e.image_eq_image_inter_ground, ←e.image_eq_image_inter_ground ]

lemma iso.preimage_compl (e : M ≃i N) (X : set β) : e.preimage Xᶜ = M.E \ e.preimage X :=
by rw [iso.preimage, preimage_compl, preimage_compl, compl_eq_univ_diff, 
    image_diff subtype.coe_injective, image_univ, subtype.range_coe, iso.preimage] 
  
lemma iso.image_compl (e : M ≃i N) (X : set α) : e.image Xᶜ = N.E \ e.image X :=
by rw [iso.image_eq_preimage_symm, iso.preimage_compl, ←iso.image_eq_preimage_symm]

lemma iso.image_diff (e : M ≃i N) (X Y : set α) : e.image (X \ Y) = e.image X \ e.image Y :=
by rw [diff_eq, e.image_inter, e.image_compl, diff_eq, ←inter_assoc, diff_eq, 
  inter_eq_self_of_subset_left (e.image_subset_ground _) ]

@[simp] lemma iso.image_empty (e : M ≃i N) : e.image ∅ = ∅ := 
by simp [iso.image]

lemma iso.image_subset_image (e : M ≃i N) {X Y : set α} (hXY : X ⊆ Y) : e.image X ⊆ e.image Y :=
by rw [←diff_eq_empty, ←e.image_diff, diff_eq_empty.mpr hXY, e.image_empty]

lemma iso.image_ground_diff (e : M ≃i N) (X : set α) : e.image (M.E \ X) = N.E \ e.image X := 
by rw [iso.image_diff, iso.image_ground]

def iso.dual (e : M ≃i N) : M﹡ ≃i N﹡ :=
{ to_equiv := e.to_equiv,
  on_base' := begin
    intro B,
    rw [dual_base_iff', dual_base_iff', ← @subtype.range_coe _ M.E, ←@subtype.range_coe _ N.E,
      and_iff_left (image_subset_range _ _), and_iff_left (image_subset_range _ _),
      ← image_univ, ←image_diff subtype.coe_injective, e.on_base', ←image_univ, 
      ← image_diff subtype.coe_injective, equiv.to_fun_as_coe, image_diff (equiv.injective _), 
        image_univ, equiv.range_eq_univ],
  end  }

lemma iso.on_base (e : M ≃i N) {B : set α} (hI : B ⊆ M.E) : M.base B ↔ N.base (e.image B) := 
begin
  rw ←@subtype.range_coe _ M.E at hI, 
  obtain ⟨B, rfl⟩ := subset_range_iff_exists_image_eq.mp hI,  
  rw [iso.image, e.on_base', equiv.to_fun_as_coe], 
  convert iff.rfl using 1, 
  simp only [subtype.preimage_image_coe, eq_iff_iff], 
  refl, 
end 

lemma iso.on_indep (e : M ≃i N) {I : set α} (hI : I ⊆ M.E) : 
  M.indep I ↔ N.indep (e.image I) :=
begin
  rw [indep_iff_subset_base, indep_iff_subset_base], 
  split, 
  { rintro ⟨B, hB, hIB⟩,
    exact ⟨e.image B, (e.on_base hB.subset_ground).mp hB, e.image_subset_image hIB⟩ },
  rintro ⟨B, hB, hIB⟩, 
  refine ⟨e.preimage B, _, _⟩, 
  { rwa [iso.preimage_eq_image_symm, ←e.symm.on_base hB.subset_ground] },
  rw [←e.preimage_image hI, e.preimage_eq_image_symm, e.preimage_eq_image_symm],
  apply e.symm.image_subset_image hIB, 
end 

end equiv

section restriction -- taken from restriction.lean

variables {α : Type*} {I J B B' B₁ B₂ X Y R : set α} {e f : α} {M N : matroid_in α}

/-- Restrict the matroid `M` to `X : set α`.  -/
def restrict (M : matroid_in α) (X : set α) : matroid_in α :=
matroid_of_indep (X ∩ M.E) (λ I, M.indep I ∧ I ⊆ X ∩ M.E) ⟨M.empty_indep, empty_subset _⟩ 
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
( by tauto )   

@[class] structure has_restrict (α β : Type*) := (restrict : α → β → α)

infix ` ‖ ` :75 :=  has_restrict.restrict 

instance : has_restrict (matroid_in α) (set α) := ⟨λ M E, M.restrict E⟩  

@[simp] lemma restrict_indep_iff : (M ‖ R).indep I ↔ M.indep I ∧ I ⊆ R :=
begin
  unfold has_restrict.restrict, rw [restrict], 
  simp only [subset_inter_iff, matroid_of_indep_apply, and.congr_right_iff, and_iff_left_iff_imp],  
  refine λ hI h, hI.subset_ground, 
end 

lemma indep.indep_restrict_of_subset (h : M.indep I) (hIR : I ⊆ R) : (M ‖ R).indep I := 
restrict_indep_iff.mpr ⟨h,hIR⟩

lemma restrict_ground_eq' : (M ‖ R).E = R ∩ M.E := rfl 

@[simp] lemma restrict_ground_eq (hR : R ⊆ M.E . ssE) : (M ‖ R).E = R := 
by rwa [restrict_ground_eq', inter_eq_left_iff_subset]

lemma restrict_restrict (R₁ R₂ : set α) : (M ‖ R₁) ‖ R₂ = M ‖ (R₁ ∩ R₂) := 
eq_of_indep_iff_indep_forall 
(by rw [restrict_ground_eq', inter_comm, restrict_ground_eq', restrict_ground_eq', inter_right_comm]) 
(λ I hI, by simp [and_assoc])

lemma restrict_restrict_of_subset {R₁ R₂ : set α} (hR : R₂ ⊆ R₁) : (M ‖ R₁) ‖ R₂ = M ‖ R₂ :=
by rw [restrict_restrict, inter_eq_self_of_subset_right hR]

lemma restrict_eq_restrict_iff {R₁ R₂ : set α} : M ‖ R₁ = M ‖ R₂ ↔ R₁ ∩ M.E = R₂ ∩ M.E :=
begin
  simp only [eq_iff_indep_iff_indep_forall, subset_inter_iff, restrict_ground_eq', 
    restrict_indep_iff, and.congr_right_iff, and_imp, and_iff_left_iff_imp], 
  intros h_eq I hIR₁ hIE hI, 
  rw [iff_true_intro hIR₁, true_iff], 
  exact (subset_inter hIR₁ hIE).trans (h_eq.trans_subset (inter_subset_left _ _)), 
end 

lemma restrict_inter_ground (M : matroid_in α) (R : set α) : M ‖ (R ∩ M.E) = M ‖ R := 
by rw [restrict_eq_restrict_iff, inter_assoc, inter_self]

@[simp] lemma restrict_base_iff (hX : X ⊆ M.E . ssE) : (M ‖ X).base I ↔ M.basis I X := 
begin
  rw [base_iff_mem_maximals, basis_iff_mem_maximals], 
  conv {to_lhs, congr, skip, congr, skip, congr, funext, rw restrict_indep_iff}, 
  refl, 
end 

@[simp] lemma basis.base_restrict (h : M.basis I X) : (M ‖ X).base I := 
restrict_base_iff.mpr h

lemma basis.basis_restrict_of_subset (hI : M.basis I X) (hXY : X ⊆ Y) (hY : Y ⊆ M.E . ssE) : 
  (M ‖ Y).basis I X :=
by { rwa [←restrict_base_iff, restrict_restrict_of_subset hXY, restrict_base_iff], simpa }

lemma restrict_eq_self_iff : M ‖ X = M ↔ M.E ⊆ X := 
begin
  simp only [eq_iff_indep_iff_indep_forall, restrict_indep_iff, and_iff_left_iff_imp, 
    restrict_ground_eq', inter_eq_right_iff_subset], 
  exact λ h I hI hI', hI.trans (inter_subset_left _ _), 
end   

noncomputable def restrict_iso {β : Type*} {N : matroid_in β} (i : M ≃i N) (R : set α) : 
  M ‖ R ≃i (N ‖ i.image R) := 
let f : (M ‖ R).E → β := λ x, i ⟨x, mem_of_mem_of_subset x.prop (inter_subset_right _ _)⟩, 
    hf : f.injective := λ x y hxy, subtype.coe_inj.mp (by simpa using subtype.coe_inj.mp hxy) in 
  iso_of_indep ((equiv.of_injective f hf).trans (equiv.set.of_eq 
    (begin
      simp_rw [restrict_ground_eq'], 
      rw [inter_eq_self_of_subset_left (iso.image_subset_ground _ _), iso.image, 
        subset_antisymm_iff], 
      simp only [image_subset_iff], 
      split, 
      { rintro y ⟨⟨x,hx⟩, rfl⟩,
        exact ⟨i ⟨x, (inter_subset_right _ _) hx⟩, ⟨⟨x, hx.2⟩ , hx.1, rfl⟩, rfl⟩ },
      rintro x (hx : coe x ∈ R), 
      simp only [mem_preimage, mem_range, set_coe.exists], 
      refine ⟨x, ⟨hx,x.2⟩, _⟩, 
      simp [subtype.coe_inj], 
    end))) 
  (begin
    intros I, 
    simp only [image_subset_iff, subtype.coe_mk, restrict_indep_iff, equiv.coe_trans, 
      function.comp_app, equiv.of_injective_apply, equiv.set.of_eq_apply], 
    rw [i.on_indep, and_iff_left, and_iff_left], 
    { convert iff.rfl using 2,  
      unfold iso.image, 
      rw [subset_antisymm_iff], split, 
      { rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩,
        exact ⟨i ⟨z, (inter_subset_right _ _) z.prop⟩, ⟨_, by simpa, rfl⟩, rfl⟩ },
      rintro x ⟨y, ⟨⟨z,hzE⟩,⟨⟨w,hw⟩, hwI, (rfl : w = z)⟩,rfl⟩, rfl⟩, 
      rw [restrict_ground_eq', mem_inter_iff] at hw, 
      exact ⟨⟨i ⟨w,hzE⟩, ⟨⟨i ⟨w,hzE⟩,⟨_,by simpa using hw.1,rfl⟩,rfl⟩,by simp⟩⟩,
        ⟨⟨w,hw⟩,hwI,rfl⟩,rfl⟩ },
    { rintro ⟨x,hxR,hxE⟩ hxI, 
      simp only [mem_preimage, subtype.coe_mk], 
      exact ⟨i ⟨x, _⟩,⟨_, by simpa, rfl⟩,rfl⟩ },
    { rintro ⟨x,hxR,hxE⟩ hxI, exact hxR }, 
    rintro _ ⟨⟨x,hxR,hxE⟩, hI, rfl⟩, 
    exact hxE, 
  end)

lemma basis.transfer (hIX : M.basis I X) (hJX : M.basis J X) (hXY : X ⊆ Y) (hJY : M.basis J Y) : 
  M.basis I Y :=
begin
  rw [←restrict_base_iff], 
  exact (restrict_base_iff.mpr hJY).base_of_basis_supset hJX.subset 
    (hIX.basis_restrict_of_subset hXY), 
end 

lemma indep.exists_basis_subset_union_basis (hI : M.indep I) (hIX : I ⊆ X) (hJ : M.basis J X) : 
  ∃ I', M.basis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J :=
begin
  obtain ⟨I', hI', hII', hI'IJ⟩ := 
    (hI.indep_restrict_of_subset hIX).exists_base_subset_union_base (basis.base_restrict hJ), 
  exact ⟨I', restrict_base_iff.mp hI', hII', hI'IJ⟩, 
end 

lemma basis.base_of_base_subset (hIX : M.basis I X) (hB : M.base B) (hBX : B ⊆ X) : M.base I :=
hB.base_of_basis_supset hBX hIX

lemma basis.eq_exchange_of_diff_eq_singleton (hI : M.basis I X) (hJ : M.basis J X) 
(hIJ : I \ J = {e}) : 
  ∃ f ∈ J \ I, J = (insert f I) \ {e} :=
by { rw [←restrict_base_iff] at hI hJ, exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ }

lemma basis.encard_eq_encard_of_basis (hIX : M.basis I X) (hJX : M.basis J X) : 
  I.encard = J.encard :=
by { rw [←restrict_base_iff] at hIX hJX, exact hIX.encard_eq_encard_of_base hJX }

lemma basis.card_eq_card_of_basis (hIX : M.basis I X) (hJX : M.basis J X) : I.ncard = J.ncard :=
by { rw [←restrict_base_iff] at hIX hJX, exact hIX.card_eq_card_of_base hJX }

lemma indep.augment_of_finite (hI : M.indep I) (hJ : M.indep J) (hIfin : I.finite) 
(hIJ : I.ncard < J.ncard) :
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
begin
  obtain ⟨K, hK, hIK⟩ :=  
    (hI.indep_restrict_of_subset (subset_union_left I J)).exists_base_supset, 
  obtain ⟨K', hK', hJK'⟩ :=
    (hJ.indep_restrict_of_subset (subset_union_right I J)).exists_base_supset, 
  have hJfin := finite_of_ncard_pos ((nat.zero_le _).trans_lt hIJ), 
  rw restrict_base_iff at hK hK', 
  have hK'fin := (hIfin.union hJfin).subset hK'.subset, 
  have hlt := 
    hIJ.trans_le ((ncard_le_of_subset hJK' hK'fin).trans_eq (hK'.card_eq_card_of_basis hK)), 
  obtain ⟨e,he⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt hIfin, 
  exact ⟨e, (hK.subset he.1).elim (false.elim ∘ he.2) id, 
    he.2, hK.indep.subset (insert_subset.mpr ⟨he.1,hIK⟩)⟩, 
end 

end restriction

section closure -- taken from closure.lean

variables {α : Type*} {M : matroid_in α} {I J B C X Y : set α} {e f x y : α}

/-- A flat is a maximal set having a given basis  -/
def flat (M : matroid_in α) (F : set α) : Prop := 
(∀ ⦃I X⦄, M.basis I F → M.basis I X → X ⊆ F) ∧ F ⊆ M.E  

lemma ground_flat (M : matroid_in α) : M.flat M.E := 
⟨λ _ _ _, basis.subset_ground, subset.rfl⟩

/-- The closure of a subset of the ground set is the intersection of the flats containing it. 
  A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.cl X := M.cl (X ∩ M.E)`. -/
def cl (M : matroid_in α) (X : set α) : set α := ⋂₀ {F | M.flat F ∧ X ∩ M.E ⊆ F} 

lemma cl_def (M : matroid_in α) (X : set α) : M.cl X = ⋂₀ {F | M.flat F ∧ X ∩ M.E ⊆ F} := rfl

lemma cl_eq_sInter_of_subset (X : set α) (hX : X ⊆ M.E . ssE) : 
  M.cl X = ⋂₀ {F | M.flat F ∧ X ⊆ F} :=
by rw [cl, inter_eq_self_of_subset_left hX]

lemma cl_eq_cl_inter_ground (M : matroid_in α) (X : set α) : M.cl X = M.cl (X ∩ M.E) :=
by rw [cl_def, cl_eq_sInter_of_subset]

lemma inter_ground_subset_cl (M : matroid_in α) (X : set α) : X ∩ M.E ⊆ M.cl X := 
by { rw [cl_eq_cl_inter_ground], simp [cl_def] }

@[ssE_finish_rules] lemma cl_subset_ground (M : matroid_in α) (X : set α) : M.cl X ⊆ M.E := 
begin
  apply sInter_subset_of_mem, 
  simp only [mem_set_of_eq, inter_subset_right, and_true], 
  apply ground_flat, 
end 

lemma mem_cl_iff_forall_mem_flat (X : set α) (hX : X ⊆ M.E . ssE) : 
  e ∈ M.cl X ↔ ∀ F, M.flat F → X ⊆ F → e ∈ F :=
by simp_rw [cl_eq_sInter_of_subset, mem_sInter, mem_set_of_eq, and_imp]

lemma subset_cl (M : matroid_in α) (X : set α) (hX : X ⊆ M.E . ssE) : X ⊆ M.cl X :=
by { rw [cl_eq_sInter_of_subset, subset_sInter_iff], simp }

lemma flat.cl {F : set α} (hF : M.flat F) : M.cl F = F :=
(sInter_subset_of_mem (by simpa)).antisymm (M.subset_cl F hF.2)

@[simp] lemma cl_ground (M : matroid_in α) : M.cl M.E = M.E := 
(cl_subset_ground M M.E).antisymm (M.subset_cl _)

@[simp] lemma cl_cl (M : matroid_in α) (X : set α) : M.cl (M.cl X) = M.cl X :=
begin
  nth_rewrite 2 cl_eq_cl_inter_ground, 
  nth_rewrite 1 cl_eq_cl_inter_ground, 
  refine (M.subset_cl _ (cl_subset_ground _ _)).antisymm' (λ e he, _), 
  rw mem_cl_iff_forall_mem_flat at *,
  refine λ F hF hXF, he _ hF (λ f hf, _), 
  rw mem_cl_iff_forall_mem_flat at hf, 
  exact hf _ hF hXF, 
end

lemma cl_subset (M : matroid_in α) (h : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
begin
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground Y], 
  refine sInter_subset_sInter _, 
  simp only [ground_inter_left, set_of_subset_set_of, and_imp],
  exact λ F hF hiF, ⟨hF, subset_trans (inter_subset_inter_left _ h) hiF⟩, 
end

lemma cl_mono (M : matroid_in α) : monotone M.cl :=
begin
  intros X Y h,
  nth_rewrite 1 cl_eq_cl_inter_ground,
  rw cl_eq_cl_inter_ground,
  apply cl_subset,
  exact inter_subset_inter_left M.E h
end

lemma cl_subset_cl (hXY : X ⊆ M.cl Y) : M.cl X ⊆ M.cl Y :=
by simpa only [cl_cl] using M.cl_subset hXY

lemma cl_subset_cl_iff_subset_cl' : (X ⊆ M.E ∧ M.cl X ⊆ M.cl Y) ↔ X ⊆ M.cl Y :=
⟨λ h, (M.subset_cl _ h.1).trans h.2, λ h, ⟨h.trans (cl_subset_ground _ _), cl_subset_cl h⟩ ⟩

lemma cl_subset_cl_iff_subset_cl (hX : X ⊆ M.E . ssE) : M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
begin
  nth_rewrite 1 [←cl_subset_cl_iff_subset_cl'], 
  rw [and_iff_right hX],
end

lemma mem_cl_of_mem (M : matroid_in α) (h : x ∈ X) (hX : X ⊆ M.E . ssE) : x ∈ M.cl X :=
(M.subset_cl X hX) h

lemma mem_cl_of_mem' (M : matroid_in α) (h : e ∈ X) (hX : e ∈ M.E . ssE) : e ∈ M.cl X :=
by { rw [cl_eq_cl_inter_ground], apply mem_cl_of_mem, exact ⟨h, hX⟩ }

@[simp] lemma cl_union_cl_right_eq (M : matroid_in α) (X Y : set α) :
  M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) :=
begin
  refine subset_antisymm _ _, 
  { rw [cl_eq_cl_inter_ground, inter_distrib_right, ←cl_cl _ (X ∪ Y) ],
    refine M.cl_subset 
      (union_subset ((inter_ground_subset_cl _ _).trans (cl_subset _ (subset_union_left _ _))) _), 
      rw [ground_inter_left], 
      exact (cl_subset _ (subset_union_right _ _)) },
  rw [cl_eq_cl_inter_ground, inter_distrib_right], 
  exact cl_subset _ (union_subset ((inter_subset_left _ _).trans (subset_union_left _ _)) 
    ((inter_ground_subset_cl _ _).trans (subset_union_right _ _))), 
end

@[simp] lemma cl_insert_cl_eq_cl_insert (M : matroid_in α) (e : α) (X : set α) :
  M.cl (insert e (M.cl X)) = M.cl (insert e X) :=
by simp_rw [←singleton_union, cl_union_cl_right_eq]

lemma indep.cl_eq_set_of_basis (hI : M.indep I) : M.cl I = {x | M.basis I (insert x I)} :=
begin
  set F := {x | M.basis I (insert x I)} with hF, 

  have hIF : M.basis I F,
  { rw basis_iff, 
    refine ⟨hI, (λ e he, by { rw [hF, mem_set_of, insert_eq_of_mem he], exact hI.basis_self }), 
      λ J hJ hIJ hJF, hIJ.antisymm (λ e he, _)⟩,
    rw basis.eq_of_subset_indep (hJF he) (hJ.subset (insert_subset.mpr ⟨he, hIJ⟩)) 
      (subset_insert _ _) subset.rfl, 
    exact mem_insert _ _,
    rw hF, rintros e ⟨_, he⟩,
    rw ←singleton_union at he,
    exact singleton_subset_iff.mp (union_subset_iff.mp he).1 },
  
  have hF : M.flat F, 
  {
    refine ⟨
      λ J Y hJF hJY y hy, (indep.basis_of_forall_insert hI (subset_insert _ _) (λ e he, _) (insert_subset.mpr ⟨hJY.subset_ground hy, by ssE⟩)),
      hIF.subset_ground
    ⟩,
    refine (basis.insert_dep (hIF.transfer hJF (subset_union_right _ _) (hJY.basis_union hJF)) (mem_of_mem_of_subset he _)).1,
    rw [diff_subset_iff, union_diff_self, insert_subset], 
    simp only [mem_union, subset_union_left, and_true],
    right, left, exact hy
  },

  rw [subset_antisymm_iff, cl, subset_sInter_iff],
  refine ⟨sInter_subset_of_mem ⟨hF, (inter_subset_left I M.E).trans hIF.subset⟩, _⟩,
  rintro F' ⟨hF', hIF'⟩ e (he : M.basis I (insert e I)),
  rw (inter_eq_left_iff_subset.mpr (hIF.subset.trans hIF.subset_ground)) at hIF',
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF' hF'.2,

  exact (hF'.1 hJ (he.basis_union_of_subset hJ.indep hIJ)) (or.inr (mem_insert _ _)),
end

lemma indep.mem_cl_iff' (hI : M.indep I) : 
  x ∈ M.cl I ↔ (x ∈ M.E ∧ (M.indep (insert x I) → x ∈ I)) :=
begin
  simp_rw [hI.cl_eq_set_of_basis, mem_set_of_eq],
  refine ⟨λ h, ⟨h.subset_ground (mem_insert _ _), λ h', h.mem_of_insert_indep (mem_insert _ _) h'⟩, 
    λ h, _⟩, 
  refine hI.basis_of_forall_insert (subset_insert x I) (λ e he hei, he.2  _) 
    (insert_subset.mpr ⟨h.1, hI.subset_ground⟩), 
  rw [←singleton_union, union_diff_right, mem_diff, mem_singleton_iff] at he,
  rw [he.1] at ⊢ hei, 
  exact h.2 hei,
end

lemma indep.mem_cl_iff (hI : M.indep I) (hx : x ∈ M.E . ssE) : 
  x ∈ M.cl I ↔ (M.indep (insert x I) → x ∈ I) :=
begin
  simp_rw [hI.mem_cl_iff', and_iff_right_iff_imp],
  intro _, exact hx
end

lemma indep.mem_cl_iff_insert_dep_or_mem (hI : M.indep I) :
  x ∈ M.cl I ↔ M.dep (insert x I) ∨ x ∈ I :=
begin
  rw [hI.mem_cl_iff', dep_iff, insert_subset, and_iff_left hI.subset_ground, imp_iff_not_or], 
  refine (em' (x ∈ M.E)).elim (λ hxE, _) (by tauto), 
  rw [iff_false_intro hxE, false_and, and_false, false_or, false_iff], 
  exact not_mem_subset hI.subset_ground hxE
end 

lemma indep.insert_dep_iff (hI : M.indep I) :
  M.dep (insert e I) ↔ e ∈ M.cl I \ I :=
begin
  rw [mem_diff, hI.mem_cl_iff_insert_dep_or_mem, or_and_distrib_right, and_not_self, or_false,
    iff_self_and], 
  refine λ hd heI, hd.not_indep _,
  rwa [insert_eq_of_mem heI], 
end  

lemma indep.mem_cl_iff_of_not_mem (hI : M.indep I) (heI : e ∉ I) : 
  e ∈ M.cl I ↔ M.dep (insert e I) :=
by { rw [hI.mem_cl_iff', dep_iff, insert_subset, and_iff_left hI.subset_ground], tauto }

lemma indep.not_mem_cl_iff (hI : M.indep I) (he : e ∈ M.E . ssE) :
  e ∉ M.cl I ↔ (e ∉ I ∧ M.indep (insert e I)) :=
by rw [←not_iff_not, not_not_mem, and_comm, not_and, hI.mem_cl_iff, not_not_mem]

lemma Inter_cl_eq_cl_Inter_of_Union_indep {ι : Type*} (I : ι → set α) [hι : nonempty ι]
  (h : M.indep (⋃ i, I i)) : (⋂ i, M.cl (I i)) = M.cl (⋂ i, I i) :=
begin  
  have hi : ∀ i, M.indep (I i), from λ i, h.subset (subset_Union _ _), 
  refine subset.antisymm _ (subset_Inter (λ i, M.cl_subset (Inter_subset _ _))), 
  rintro e he, rw mem_Inter at he, 
  by_contra h',
  obtain i₀ := hι.some,
  have hiu : (⋂ i , I i) ⊆ ⋃ i, I i, from 
    ((Inter_subset _ i₀).trans (subset_Union _ i₀)), 
  have hi_inter : M.indep (⋂ i, I i), from (hi i₀).subset (Inter_subset _ _), 
  rw hi_inter.not_mem_cl_iff ((M.cl_subset_ground (I i₀)) (he i₀)) at h',
  rw mem_Inter at h',
  rw not_forall at h', 
  { obtain ⟨⟨i₁, hei₁⟩, hei⟩ := h',   

    have hdi₁ : ¬M.indep (insert e (I i₁)),
      from λ h_ind, hei₁ (((hi i₁).mem_cl_iff'.mp (he i₁)).2 h_ind),
    
    have heu : e ∉ ⋃ i, I i, from λ he, hdi₁ (h.subset (insert_subset.mpr ⟨he, subset_Union _ _⟩)), 
    
    have hd_all : ∀ i, ¬M.indep (insert e (I i)), 
      from λ i hind, heu (mem_Union_of_mem _ (((hi i).mem_cl_iff'.mp (he i)).2 hind)),
    
    have hb : M.basis (⋃ i, I i) (insert e (⋃ i, I i)), 
    { have h' := (M.cl_subset) (subset_Union _ _) (he i₀),
      rwa [h.cl_eq_set_of_basis] at h' },
    
    obtain ⟨I', hI', hssI', hI'ss⟩ := 
      hei.exists_basis_subset_union_basis (insert_subset_insert hiu) hb, 
    
    rw [insert_union, union_eq_right_iff_subset.mpr hiu] at hI'ss, 
    
    have hI'I : I' \ (⋃ i, I i) = {e}, 
    { refine subset.antisymm _ (singleton_subset_iff.mpr ⟨hssI' (mem_insert _ _),heu⟩),
      rwa [diff_subset_iff, union_singleton] }, 
    
    obtain ⟨f, hfI, hf⟩ := hI'.eq_exchange_of_diff_eq_singleton hb hI'I, 

    have hf' : ∀ i, f ∈ I i, 
    { refine λ i, by_contra (λ hfi, (hd_all i (hI'.indep.subset (insert_subset.mpr ⟨_,_⟩)))), 
      { exact hssI' (mem_insert _ _) },
      rw [←diff_singleton_eq_self hfi, diff_subset_iff, singleton_union], 
      exact ((subset_Union _ i).trans_eq hf).trans (diff_subset _ _) },   

    exact hfI.2 (hssI' (or.inr (by rwa mem_Inter))),
  },
end 

lemma bInter_cl_eq_cl_sInter_of_sUnion_indep (Is : set (set α)) (hIs : Is.nonempty) (h : M.indep (⋃₀ Is)) :
  (⋂ I ∈ Is, M.cl I) = M.cl (⋂₀ Is) :=
begin
  rw [sUnion_eq_Union] at h, 
  rw [bInter_eq_Inter, sInter_eq_Inter],
  haveI := hIs.to_subtype,
  exact Inter_cl_eq_cl_Inter_of_Union_indep (λ (x : Is), coe x) h, 
end 

lemma basis.cl (hIX : M.basis I X) : M.cl I = M.cl X := 
(M.cl_subset hIX.subset).antisymm (cl_subset_cl 
  (λ x hx, hIX.indep.mem_cl_iff.mpr (λ h, hIX.mem_of_insert_indep hx h)))

lemma basis.mem_cl_iff (hIX : M.basis I X) (he : e ∈ M.E . ssE) : 
  e ∈ M.cl X ↔ (M.indep (insert e I) → e ∈ I) :=
by rw [←hIX.cl, hIX.indep.mem_cl_iff]

lemma basis.subset_cl (hI : M.basis I X) : X ⊆ M.cl I :=
by { rw hI.cl, exact M.subset_cl X hI.subset_ground }

lemma indep.basis_cl (hI : M.indep I) : M.basis I (M.cl I) :=
begin
  refine hI.basis_of_forall_insert (M.subset_cl I hI.subset_ground) (λ e he heI, he.2 _), 
  rw [mem_diff, hI.mem_cl_iff] at he,
  obtain ⟨he, he'⟩ := he,
  rw hI.mem_cl_iff_of_not_mem he' at he,
  exact (he.not_indep heI).elim, 
end 

lemma indep.basis_of_subset_cl (hI : M.indep I) (hIX : I ⊆ X) (h : X ⊆ M.cl I) : M.basis I X :=
hI.basis_cl.basis_subset hIX h

lemma indep.base_of_cl_eq_ground (hI : M.indep I) (h : M.cl I = M.E) : M.base I :=
by { rw base_iff_basis_ground, exact hI.basis_of_subset_cl hI.subset_ground (by rw h) }

lemma base.cl (hB : M.base B) : M.cl B = M.E :=
by { rw [(base_iff_basis_ground.mp hB).cl], exact M.cl_ground }

lemma base.mem_cl (hB : M.base B) (e : α) (he : e ∈ M.E . ssE) : e ∈ M.cl B :=
by rwa [base.cl hB]

lemma cl_diff_singleton_eq_cl (h : e ∈ M.cl (X \ {e})) : M.cl (X \ {e}) = M.cl X :=
begin
  rw [cl_eq_cl_inter_ground, diff_eq, inter_right_comm, ←diff_eq] at *, 
  rw [M.cl_eq_cl_inter_ground X], 
  set X' := X ∩ M.E with hX',
  refine (M.cl_mono (diff_subset _ _)).antisymm _,
  
  have : (X' \ { e } ⊆ M.cl (X' \ { e })),
    { refine M.subset_cl (X' \ { e }) _,
      have g := inter_subset_right X M.E,
      have : X' \ {e} ⊆ X' := by simp only [diff_singleton_subset_iff, subset_insert],
      rw ←hX' at g, exact this.trans g, },
  have h' := M.cl_mono (insert_subset.mpr ⟨h, this⟩),
  rw [insert_diff_singleton, cl_cl] at h',
  exact (M.cl_mono (subset_insert _ _)).trans h',
end

lemma mem_cl_diff_singleton_iff_cl (he : e ∈ X) (heE : e ∈ M.E . ssE):
  e ∈ M.cl (X \ {e}) ↔ M.cl (X \ {e}) = M.cl X :=
begin
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground X, diff_eq, inter_right_comm, ←diff_eq], 
  refine ⟨cl_diff_singleton_eq_cl, λ h, _⟩,
  rw [h], 
  exact M.mem_cl_of_mem' ⟨he, heE⟩, 
end 

lemma indep_iff_cl_diff_ne_forall : M.indep I ↔ (∀ e ∈ I, M.cl (I \ {e}) ≠ M.cl I) :=
begin
  refine ⟨λ hI e heI h_eq, _, λ h, _⟩,
  { have hecl : e ∈ M.cl I := M.subset_cl I (hI.subset_ground) heI, 
    rw [←h_eq] at hecl, 
    simpa only [(hI.diff {e}).mem_cl_iff, insert_diff_singleton, not_mem_diff_singleton, 
      insert_eq_of_mem heI, imp_iff_right hI] using hecl },
  have hIE : I ⊆ M.E, 
  { refine λ e he, by_contra (λ heE, h e he _), 
    rw [M.cl_eq_cl_inter_ground I, M.cl_eq_cl_inter_ground, diff_eq, inter_right_comm, 
      inter_assoc, ←diff_eq, diff_singleton_eq_self heE] },
  obtain ⟨J, hJ⟩ := M.exists_basis I, 
  convert hJ.indep,
  refine hJ.subset.antisymm' (λ e he, by_contra (λ heJ, _)), 
  have hJIe : J ⊆ I \ {e}, from subset_diff_singleton hJ.subset heJ, 
  have hcl := h e he, 
  rw [ne.def, ←mem_cl_diff_singleton_iff_cl he] at hcl, 
  have hcl' := not_mem_subset (M.cl_mono hJIe) hcl, 
  rw [hJ.cl] at hcl', 
  refine hcl' (M.subset_cl _ hJ.subset_ground he),   
end

lemma indep_iff_not_mem_cl_diff_forall (hI : I ⊆ M.E . ssE) : 
  M.indep I ↔ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
begin
  rw indep_iff_cl_diff_ne_forall,
  { refine ⟨λ h x hxI, by { rw mem_cl_diff_singleton_iff_cl hxI, exact h x hxI },
            λ h x hxI, by { rw [ne.def, ←mem_cl_diff_singleton_iff_cl hxI], exact h x hxI }⟩, },
end

lemma indep.insert_indep_iff_of_not_mem (hI : M.indep I) (he : e ∉ I) (he' : e ∈ M.E . ssE):
  M.indep (insert e I) ↔ e ∉ M.cl I :=
⟨λ h, (hI.not_mem_cl_iff he').mpr ⟨he, h⟩, λ h, ((hI.not_mem_cl_iff he').mp h).2⟩

lemma basis_iff_cl : M.basis I X ↔ I ⊆ X ∧ X ⊆ M.cl I ∧ ∀ J ⊆ I, X ⊆ M.cl J → J = I :=
begin
  split, 
  { refine λ h, ⟨h.subset, h.subset_cl, λ J hJI hXJ, hJI.antisymm (λ e heI, _)⟩, 
    rw [(h.indep.subset hJI).cl_eq_set_of_basis] at hXJ, 
    exact (h.subset.trans hXJ heI : M.basis _ _).mem_of_insert_indep (mem_insert _ _) 
      (h.indep.subset (insert_subset.mpr ⟨heI, hJI⟩)) },
  rintro ⟨hIX, hXI, hmin⟩,  
  refine indep.basis_of_forall_insert _ hIX _ _,

  { rw indep_iff_cl_diff_ne_forall,
    intros e he hecl,
    rw ← hmin _ (diff_subset _ _) (hXI.trans_eq hecl.symm) at he, 
    exact he.2 (mem_singleton e) },
  
  exact λ e he hi, he.2 
    (((hi.subset (subset_insert _ _)).basis_cl).mem_of_insert_indep (hXI (he.1)) hi),
  exact hXI.trans (M.cl_subset_ground I),
end

lemma basis_union_iff_indep_cl : M.basis I (I ∪ X) ↔ M.indep I ∧ X ⊆ M.cl I :=
begin
  refine ⟨λ h, ⟨h.indep, (subset_union_right _ _).trans h.subset_cl⟩, _⟩,
  rw basis_iff_cl,
  rintros ⟨hI, hXI⟩,
  refine ⟨subset_union_left _ _, union_subset (M.subset_cl I hI.subset_ground) hXI,
    λ J hJI hJ, by_contra (λ h', _)⟩,
  obtain ⟨e,heI,heJ⟩ := exists_of_ssubset (hJI.ssubset_of_ne h'),
  have heJ' : e ∈ M.cl J,
    from hJ (or.inl heI),
  refine indep_iff_not_mem_cl_diff_forall.mp hI e heI (mem_of_mem_of_subset heJ' _),
  exact M.cl_subset (subset_diff_singleton hJI heJ),
end

lemma basis_iff_indep_cl : M.basis I X ↔ M.indep I ∧ X ⊆ M.cl I ∧ I ⊆ X :=
⟨λ h, ⟨h.indep, h.subset_cl, h.subset⟩,
  λ h, (basis_union_iff_indep_cl.mpr ⟨h.1,h.2.1⟩).basis_subset h.2.2 (subset_union_right _ _)⟩

variables {S T : set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains 
  a base of `M`. -/
def spanning (M : matroid_in α) (S : set α) := M.cl S = M.E ∧ S ⊆ M.E 

@[ssE_finish_rules] lemma spanning.subset_ground (hS : M.spanning S) : S ⊆ M.E := 
hS.2 

lemma spanning.cl (hS : M.spanning S) : M.cl S = M.E := 
hS.1

lemma spanning_iff_cl (hS : S ⊆ M.E . ssE) : M.spanning S ↔ M.cl S = M.E := 
⟨and.left, λ h, ⟨h,hS⟩⟩

lemma not_spanning_iff_cl (hS : S ⊆ M.E . ssE) : ¬ M.spanning S ↔ M.cl S ⊂ M.E :=
begin
  rw [spanning_iff_cl, ssubset_iff_subset_ne, ne.def, iff_and_self, 
    iff_true_intro (M.cl_subset_ground _)], 
  refine λ _, trivial,  
end  

lemma ground_spanning (M : matroid_in α) : M.spanning M.E := 
⟨M.cl_ground, rfl.subset⟩ 

lemma spanning_iff_supset_base' : M.spanning S ↔ (∃ B, M.base B ∧ B ⊆ S) ∧ S ⊆ M.E := 
begin
  rw [spanning, and.congr_left_iff], 
  refine λ hSE, ⟨λ h, _, _⟩,
  { obtain ⟨B, hB⟩ := M.exists_basis S,
    refine ⟨B, hB.indep.base_of_cl_eq_ground _, hB.subset⟩, 
    rwa [hB.cl] },
  rintro ⟨B, hB, hBS⟩, 
  rw [subset_antisymm_iff, and_iff_right (M.cl_subset_ground _), ←hB.cl], 
  exact M.cl_subset hBS, 
end 

lemma spanning_iff_supset_base (hS : S ⊆ M.E . ssE) : M.spanning S ↔ ∃ B, M.base B ∧ B ⊆ S := 
by rw [spanning_iff_supset_base', and_iff_left hS]


lemma coindep_iff_compl_spanning (hI : I ⊆ M.E . ssE) : M.coindep I ↔ M.spanning (M.E \ I) :=
begin
  simp_rw [coindep_iff_exists, spanning_iff_supset_base, subset_diff, disjoint.comm],  
  exact ⟨Exists.imp (λ B hB, ⟨hB.1, hB.1.subset_ground, hB.2⟩), 
    Exists.imp (λ B hB, ⟨hB.1, hB.2.2⟩)⟩, 
end 

lemma coindep_iff_cl_compl_eq_ground (hK : X ⊆ M.E . ssE) : M.coindep X ↔ M.cl (M.E \ X) = M.E :=
by rw [coindep_iff_compl_spanning, spanning_iff_cl]

lemma coindep.cl_compl (hX : M.coindep X) : M.cl (M.E \ X) = M.E := 
(coindep_iff_cl_compl_eq_ground hX.subset_ground).mp hX 

end closure


section circuit -- taken from circuit.lean

variables {α : Type*} {M M₁ M₂ : matroid_in α} 
  {I C C' C₁ C₂ X : set α} {e f : α}

lemma circuit.dep (hC : M.circuit C) : M.dep C := hC.1

@[ssE_finish_rules] lemma circuit.subset_ground (hC : M.circuit C) : C ⊆ M.E :=
hC.dep.subset_ground

lemma circuit.ssubset_indep (hC : M.circuit C) (hXC : X ⊂ C) : M.indep X := 
begin
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)],
  rw [circuit, mem_minimals_set_of_iff] at hC, 
  exact λ h, hXC.ne.symm (hC.2 h hXC.subset),     
end 

lemma circuit_iff : M.circuit C ↔ M.dep C ∧ (∀ I, M.dep I → I ⊆ C → I = C) :=
by { rw [circuit, mem_minimals_set_of_iff], tauto }
  
lemma circuit_iff_forall_ssubset : M.circuit C ↔ M.dep C ∧ ∀ I ⊂ C, M.indep I := 
begin
  simp_rw [circuit_iff, ssubset_iff_subset_ne, and.congr_right_iff], 
  exact λ hC, ⟨λ h I hIC, indep_of_not_dep (hIC.2 ∘ (λ hD, h _ hD hIC.1)) 
    (hIC.1.trans hC.subset_ground), 
    λ h I hD hIC, by_contra (λ hne, hD.not_indep (h _ ⟨hIC, hne⟩))⟩,
end

lemma circuit.diff_singleton_indep (hC : M.circuit C) (he : e ∈ C) : M.indep (C \ {e}) :=
hC.ssubset_indep (diff_singleton_ssubset.2 he)

lemma circuit.diff_singleton_basis (hC : M.circuit C) (he : e ∈ C) : M.basis (C \ {e}) C :=
begin
  refine (hC.diff_singleton_indep he).basis_of_forall_insert (diff_subset _ _) (λ f hf hI, _),
  simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf, 
  have := hf.2 (hf.1), subst this, 
  rw [insert_diff_singleton, insert_eq_of_mem he] at hI, 
  exact hC.dep.not_indep hI, 
end 

lemma circuit.nonempty (hC : M.circuit C) : C.nonempty :=
by {rw set.nonempty_iff_ne_empty, rintro rfl, exact hC.1.1 M.empty_indep}

lemma empty_not_circuit (M : matroid_in α) : ¬M.circuit ∅ :=
λ h, by simpa using h.nonempty

lemma circuit_iff_dep_forall_diff_singleton_indep :
  M.circuit C ↔ M.dep C ∧ ∀ e ∈ C, M.indep (C \ {e}) :=
begin
  rw [circuit_iff_forall_ssubset, and.congr_right_iff],
  refine λ hdep, ⟨λ h e heC, (h _ $ diff_singleton_ssubset.2 heC), λ h I hIC, _⟩,
  obtain ⟨e, heC,heI⟩ := exists_of_ssubset hIC,
  exact (h e heC).subset (subset_diff_singleton hIC.subset heI),
end

lemma circuit.eq_of_dep_subset_self (hC : M.circuit C) (hX : M.dep X) (hXC : X ⊆ C) : C = X :=
by_contra (λ h, hX.not_indep (hC.ssubset_indep (ssubset_of_subset_of_ne hXC (ne.symm h))))

lemma circuit.eq_of_subset_circuit (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ⊆ C₂) :
  C₁ = C₂ :=
(hC₂.eq_of_dep_subset_self hC₁.dep h).symm

/-- For an independent set `I` that spans a point `e ∉ I`, the unique circuit contained in 
`I ∪ {e}`. Has the junk value `{e}` if `e ∈ I` and `univ` if `e ∉ M.cl I`. -/
def fund_circuit (M : matroid_in α) (e : α) (I : set α) := insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.cl J})

lemma fund_circuit_subset_ground (heI : e ∈ M.cl I) : M.fund_circuit e I ⊆ M.E := 
begin
  refine (insert_subset.mpr ⟨(cl_subset_ground _ _) heI, 
    (sInter_subset_of_mem _).trans (inter_subset_right I M.E)⟩), 
  refine ⟨inter_subset_left _ _,_⟩,   
  rwa [←cl_eq_cl_inter_ground], 
end 

lemma fund_circuit_subset_insert (he : e ∈ M.cl I) : 
  M.fund_circuit e I ⊆ insert e I :=
insert_subset_insert (sInter_subset_of_mem ⟨rfl.subset, he⟩)

lemma mem_fund_circuit (M : matroid_in α) (e : α) (I : set α) : e ∈ fund_circuit M e I := 
  mem_insert _ _

/-- The fundamental circuit of `e` and `I` has the junk value `{e}` if `e ∈ I` -/
lemma indep.fund_circuit_eq_of_mem (hI : M.indep I) (he : e ∈ I) : M.fund_circuit e I = {e} :=
begin
  rw [fund_circuit, ←union_singleton, union_eq_right_iff_subset], 
  refine sInter_subset_of_mem _, 
  simp only [mem_set_of_eq, singleton_subset_iff, and_iff_right he], 
  exact mem_cl_of_mem _ (mem_singleton _) (singleton_subset_iff.mpr (by ssE)), 
end 

lemma indep.fund_circuit_circuit (hI : M.indep I) (he : e ∈ M.cl I \ I) : 
  M.circuit (M.fund_circuit e I) :=
begin
  rw [circuit_iff_dep_forall_diff_singleton_indep, 
    ←not_indep_iff (fund_circuit_subset_ground he.1), fund_circuit], 
  have hu : M.indep (⋃₀ {J : set α | J ⊆ I ∧ e ∈ M.cl J}), 
    from hI.subset (sUnion_subset (λ J, and.left)), 
  have hI' : I ∈ {J : set α | J ⊆ I ∧ e ∈ M.cl J}, from ⟨rfl.subset, he.1⟩,  
  refine ⟨λ hi, _, λ f hf, _⟩,  
  { rw [indep.insert_indep_iff_of_not_mem, ←bInter_cl_eq_cl_sInter_of_sUnion_indep _ ⟨I, hI'⟩ hu] 
      at hi, 
    { simpa using hi },
    { exact hI.subset (sInter_subset_of_mem hI') },
    exact λ heIs, he.2 (sInter_subset_of_mem hI' heIs) },
  obtain (rfl | hne) := em (e = f), 
  { refine hu.subset _, 
    simp only [insert_diff_of_mem, mem_singleton], 
    exact subset_trans (diff_subset _ _) 
      ((sInter_subset_of_mem hI').trans (subset_sUnion_of_mem hI')) },
  rw [mem_insert_iff, mem_sInter, eq_comm, iff_false_intro hne, false_or] at hf, 
  
  have hi : M.indep (⋂₀ {J : set α | J ⊆ I ∧ e ∈ M.cl J} \ {f}), 
  { exact hI.subset ((diff_subset _ _).trans (sInter_subset_of_mem hI')) },  
  rw [←insert_diff_singleton_comm hne, hi.insert_indep_iff_of_not_mem], 
  
  { intro hcl, 
    exact (hf _ ⟨(diff_subset _ _).trans (sInter_subset_of_mem hI'), hcl⟩).2 rfl,  },
  
  exact λ h'e, he.2 ((diff_subset _ _).trans (sInter_subset_of_mem hI') h'e),  
end 

lemma exists_circuit_subset_of_dep (hX : M.dep X) : ∃ C ⊆ X, M.circuit C :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain (rfl | hss) := (ssubset_or_eq_of_subset hI.subset).symm,
  { exact (hX.not_indep hI.indep).elim },
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset hss, 
  have he : e ∈ M.cl I \ I := ⟨hI.subset_cl heX, heI⟩,  
  exact ⟨M.fund_circuit e I, (fund_circuit_subset_insert he.1).trans 
    (insert_subset.mpr ⟨heX, hss.subset⟩), hI.indep.fund_circuit_circuit he⟩,  
end 

lemma dep_iff_supset_circuit (hX : X ⊆ M.E . ssE) : M.dep X ↔ ∃ C ⊆ X, M.circuit C  :=
⟨exists_circuit_subset_of_dep, by { rintro ⟨C, hCX, hC⟩, exact hC.dep.supset hCX }⟩

lemma indep_iff_forall_subset_not_circuit' : M.indep I ↔ (∀ C ⊆ I, ¬ M.circuit C) ∧ I ⊆ M.E  :=
begin
  by_cases hI : I ⊆ M.E, 
  { rw [←not_iff_not, not_indep_iff], 
    simp_rw [dep_iff_supset_circuit, and_iff_left hI, not_forall, not_not] },
  exact iff_of_false (hI ∘ indep.subset_ground) (hI ∘ and.right), 
end 

lemma indep_iff_forall_subset_not_circuit (hI : I ⊆ M.E . ssE) : 
  M.indep I ↔ (∀ C ⊆ I, ¬ M.circuit C) :=
by rw [indep_iff_forall_subset_not_circuit', and_iff_left hI]

lemma circuit.subset_cl_diff_singleton (hC : M.circuit C) (e : α) : C ⊆ M.cl (C \ {e}) :=
begin
  by_cases he : e ∈ C, 
  { rw [(hC.diff_singleton_basis he).cl], exact M.subset_cl _ }, 
  rw [diff_singleton_eq_self he], exact M.subset_cl _, 
end

lemma mem_cl_iff_exists_circuit (hX : X ⊆ M.E . ssE):
  e ∈ M.cl X ↔ e ∈ X ∨ ∃ C, M.circuit C ∧ e ∈ C ∧ C ⊆ insert e X :=
begin
  refine ⟨λ h, _,_⟩,
  { by_contra' h',
    obtain ⟨I, hI⟩ := M.exists_basis X,
    have hIe : ¬ M.indep (insert e I),
    { intro hI',
      refine indep_iff_not_mem_cl_diff_forall.mp hI' e (mem_insert _ _) _,
      rwa [insert_diff_of_mem _ (mem_singleton _),
        diff_singleton_eq_self (not_mem_subset hI.subset h'.1), hI.cl]},
    have heI : e ∈ M.cl I \ I, by { rw [hI.cl], exact ⟨h, not_mem_subset hI.subset h'.1⟩ }, 
    have hC := hI.indep.fund_circuit_circuit heI, 
    exact h'.2 _ hC (mem_fund_circuit _ _ _) 
      ((fund_circuit_subset_insert heI.1).trans (insert_subset_insert hI.subset)) },
  rintro (heX | ⟨C,hC, heC, hCX⟩),
  apply mem_cl_of_mem _ heX,  
  refine (M.cl_subset _) (hC.subset_cl_diff_singleton e heC), 
  rwa [diff_subset_iff],  
end

/-- A generalization of the strong circuit elimination axiom. For finite matroids, this is 
  equivalent to the case where `ι` is a singleton type, which is the usual two-circuit version. 
  The stronger version is required for axiomatizing infinite matroids via circuits. -/
lemma circuit.strong_multi_elimination {ι : Type*} (hC : M.circuit C) (x : ι → α) (Cs : ι → set α) 
(hCs : ∀ i, M.circuit (Cs i)) (h_mem : ∀ i, (x i) ∈ C ∩ (Cs i)) 
(h_unique : ∀ i i', x i ∈ Cs i' → i = i') {z : α} (hz : z ∈ C \ ⋃ i, Cs i) :
  ∃ C', M.circuit C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ ⋃ i, (Cs i)) \ range x :=
begin
  set Y := (C ∪ ⋃ x, Cs x) \ (insert z (range x)) with hY, 
  have hYE : Y ⊆ M.E, 
  { refine (diff_subset _ _).trans (union_subset hC.subset_ground _), 
    exact (Union_subset (λ i, (hCs i).subset_ground )) },
  
  have h₁ : range x ⊆ M.cl (⋃ i, ((Cs i) \ {x i} \ (insert z (range x)))), 
  { rintro e ⟨i, rfl⟩,  
    have h' := (hCs i).subset_cl_diff_singleton (x i) (h_mem i).2, 
    refine mem_of_mem_of_subset h' (M.cl_subset _), 
    refine subset_Union_of_subset i (subset_diff.mpr ⟨rfl.subset,_⟩), 
    rw disjoint_iff_forall_ne, 
    rintro y hy z (rfl | ⟨j, rfl⟩) rfl, 
    { exact hz.2 (mem_Union_of_mem i hy.1) },
    refine hy.2 (mem_singleton_iff.mpr _), 
    rw h_unique _ _ hy.1 },
  have h₂ : range x ⊆ M.cl Y, 
  { refine h₁.trans (M.cl_subset (Union_subset (λ x, _))),  
    refine diff_subset_diff_left (subset_union_of_subset_right _ _),
    exact subset_Union_of_subset x (diff_subset _ _) },
  have h₃ : C \ {z} ⊆ M.cl Y, 
  { suffices : C \ {z} ⊆ (C \ insert z (range x)) ∪ (range x), 
    { rw [union_diff_distrib] at hY, 
      convert this.trans (union_subset_union ((subset_union_left _ _).trans_eq hY.symm) h₂), 
      rw union_eq_right_iff_subset.mpr,
      exact M.subset_cl Y },
    rw [←union_singleton, ←diff_diff, diff_subset_iff, singleton_union, ←insert_union, 
      insert_diff_singleton, ←singleton_union, union_assoc, diff_union_self], 
    exact subset_union_of_subset_right (subset_union_left _ _) _ },
  rw [←cl_subset_cl_iff_subset_cl] at h₃, 
  have h₄ := h₃ (hC.subset_cl_diff_singleton z hz.1), 
  obtain (hzY | ⟨C', hC', hzC', hCzY⟩) := mem_cl_iff_exists_circuit.mp h₄, 
  { exact ((hY.subset hzY).2 (mem_insert z _)).elim },
  
  refine ⟨C', hC', hzC', subset_diff.mpr ⟨_,_⟩⟩, 
  { exact hCzY.trans (insert_subset.mpr ⟨or.inl hz.1,diff_subset _ _⟩) },
  refine disjoint_of_subset_left hCzY _, 
  rw [←singleton_union, disjoint_union_left, disjoint_singleton_left], 
  refine ⟨not_mem_subset _ hz.2, _⟩,   
  { rintro x' ⟨i,rfl⟩, exact mem_Union_of_mem i ((h_mem i).2) },
  exact disjoint_of_subset_right (subset_insert z _) disjoint_sdiff_left,  
end 

/-- The strong circuit elimination axiom. For any two circuits `C₁,C₂` and all `e ∈ C₁ ∩ C₂` and 
  `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma circuit.strong_elimination (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (he : e ∈ C₁ ∩ C₂) 
(hf : f ∈ C₁ \ C₂) : ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.circuit C ∧ f ∈ C :=
begin
  obtain ⟨C, hC, hfC, hCss⟩  := 
    @circuit.strong_multi_elimination _ M C₁ unit hC₁ (λ _, e) (λ _, C₂) (by simpa) 
    (by simpa) (by simp) f (by simpa),   
  simp only [range_const, Union_const] at hCss, 
  exact ⟨C, hCss, hC, hfC⟩, 
end      

/-- The circuit eliminiation axiom : for any pair of distinct circuits `C₁,C₂` and any `e`, some
  circuit is contained in `C₁ ∪ C₂ \ {e}`. Traditionally this is stated with the assumption that 
  `e ∈ C₁ ∩ C₂`, but it is also true without it. -/
lemma circuit.elimination (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ≠ C₂) (e : α) : 
  ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.circuit C :=
begin
  by_contra' h',
  have he : e ∈ C₁ ∩ C₂, 
  { by_contra he, 
    refine h' C₁ (by_contra (λ h₁, _)) hC₁,
    refine h' C₂ (by_contra (λ h₂, he _)) hC₂, 
    rw [subset_diff, not_and, disjoint_singleton_right, not_not_mem] at h₁ h₂, 
    exact ⟨h₁ (subset_union_left _ _), h₂ (subset_union_right _ _)⟩ },   
  have hf : (C₁ \ C₂).nonempty,
  { rw [nonempty_iff_ne_empty, ne.def, diff_eq_empty], 
    refine λ hss, h _, 
    exact (hC₁.eq_of_subset_circuit hC₂ hss)}, 
  obtain ⟨f, hf⟩ := hf, 
  obtain ⟨C, hCss, hC,-⟩ := hC₁.strong_elimination hC₂ he hf, 
  exact h' C hCss hC, 
end  

lemma circuit.eq_fund_circuit_of_subset_insert_indep (hC : M.circuit C) (hI : M.indep I) 
(hCI : C ⊆ insert e I) : 
  C = M.fund_circuit e I := 
begin
  by_cases heE : e ∈ M.E,
  { by_contra' hne, 
    have he : e ∉ I, { intro heI, rw [insert_eq_of_mem heI] at hCI, 
      exact hC.dep.not_indep (hI.subset hCI) },
    have heI : e ∈ M.cl I \ I, 
    { rw [mem_diff, hI.mem_cl_iff_of_not_mem he, dep_iff_supset_circuit, and_iff_left he],
      exact ⟨C, hCI, hC⟩ },
    obtain ⟨C', hC'ss, hC'⟩ := hC.elimination (hI.fund_circuit_circuit heI) hne e, 
    refine hC'.dep.not_indep (hI.subset (hC'ss.trans _)), 
    rw [diff_subset_iff, singleton_union], 
    exact union_subset hCI (fund_circuit_subset_insert heI.1) }, 
  refine (hC.dep.not_indep (hI.subset (λ x hxC, (hCI hxC).elim _ id))).elim, 
  rintro rfl, 
  exact (heE (hC.subset_ground hxC)).elim, 
end 

/-- A cocircuit is the complement of a hyperplane -/
def cocircuit (M : matroid_in α) (K : set α) : Prop := M﹡.circuit K

@[simp] lemma dual_circuit_iff_cocircuit {K : set α} : M﹡.circuit K ↔ M.cocircuit K := iff.rfl 

@[ssE_finish_rules] lemma cocircuit.subset_ground (hC : M.cocircuit C) : C ⊆ M.E :=
by { rw ←dual_circuit_iff_cocircuit at hC, rw ←dual_ground, exact hC.subset_ground }

lemma coindep_iff_forall_subset_not_cocircuit' : 
  M.coindep X ↔ (∀ K ⊆ X, ¬ M.cocircuit K) ∧ X ⊆ M.E  := 
by simp [←dual_indep_iff_coindep, indep_iff_forall_subset_not_circuit']

lemma coindep_iff_forall_subset_not_cocircuit (hX : X ⊆ M.E . ssE) : 
  M.coindep X ↔ (∀ K ⊆ X, ¬ M.cocircuit K) :=
by rw [coindep_iff_forall_subset_not_cocircuit', and_iff_left hX]

lemma cocircuit_iff_mem_minimals {K : set α} : 
  M.cocircuit K ↔ K ∈ minimals (⊆) {X | ∀ B, M.base B → (X ∩ B).nonempty} :=  
begin
  simp_rw [cocircuit, circuit, mem_minimals_set_of_iff, dep_iff, dual_indep_iff_coindep, 
    dual_ground, and_imp, coindep, not_and, not_exists, not_and, not_disjoint_iff_nonempty_inter, 
    inter_comm K],  
  split, 
  { rintro ⟨⟨h, hKE⟩,h'⟩, refine ⟨h hKE, λ X hX hXK, h' (λ _, hX) (hXK.trans hKE) hXK⟩ }, 
  rintro ⟨h1, h2⟩,
  have hKE : K ⊆ M.E, 
  { rw [←inter_eq_left_iff_subset, eq_comm],
    apply h2 (λ B hB, _) (inter_subset_left _ _), 
    rw [inter_assoc, inter_eq_self_of_subset_right hB.subset_ground, inter_comm],
    exact h1 B hB }, 
  exact ⟨⟨λ _, h1,hKE⟩, λ X hX hXE hXK , h2 (hX hXE) hXK ⟩, 
end 

lemma cocircuit_iff_mem_minimals_compl_nonspanning {K : set α} : 
  M.cocircuit K ↔ K ∈ minimals (⊆) {X | ¬M.spanning (M.E \ X) } :=
begin
  convert cocircuit_iff_mem_minimals, 
  ext X, 
  simp_rw [spanning_iff_supset_base, not_exists, not_and, subset_diff, not_and, 
    not_disjoint_iff_nonempty_inter, ←and_imp, and_iff_left_of_imp base.subset_ground, 
    inter_comm X], 
end 

end circuit

section flat -- taken from flat'.lean

variables {α : Type*} {M : matroid_in α} {I B C X Y Z K F F₀ F₁ F₂ H H₁ H₂ : set α}
          { e f x y z : α }

lemma flat_def : M.flat F ↔ ((∀ I X, M.basis I F → M.basis I X → X ⊆ F) ∧ F ⊆ M.E) := iff.rfl
/- added `∧ F ⊆ M.E` to RHS.
   Here it is the last clause as in the definition, but 
   in closure.lean I wrote similar assumptions
   as the first clause. -/

@[ssE_finish_rules] lemma flat.subset_ground (hF : M.flat F) : F ⊆ M.E :=
hF.2

lemma flat.eq_ground_of_spanning (hF : M.flat F) (h : M.spanning F) : F = M.E := 
by rw [←hF.cl, h.cl]

lemma flat.spanning_iff (hF : M.flat F) : M.spanning F ↔ F = M.E := 
⟨hF.eq_ground_of_spanning, by { rintro rfl, exact M.ground_spanning }⟩

lemma flat.Inter {ι : Type*} [hι : nonempty ι] (F : ι → set α) (hF : ∀ i, M.flat (F i)) :
  M.flat (⋂ i, F i) :=
begin
  split,
  { refine λ I X hI hIX, subset_Inter (λ i, _),
    obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset
      ((hI.subset.trans (Inter_subset _ _ ) : I ⊆ F i)),

    have hF' := hF i, rw flat_def at hF',
    refine (union_subset_iff.mp (hF'.1 _ (F i ∪ X) hIJ _)).2, 
    rw [←union_eq_left_iff_subset.mpr hIJ.subset, union_assoc],
    exact hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ), },
  intros e he, obtain i₀ := hι.some,
  rw mem_Inter at he,
  exact (flat.subset_ground (hF i₀)) (he i₀),
end

lemma flat_of_cl (M : matroid_in α) (X : set α) : M.flat (M.cl X) :=
begin
  rw [M.cl_def X, sInter_eq_Inter],
  apply flat.Inter _,
  { rintro ⟨F,hF⟩, exact hF.1 },
  use [M.E, M.ground_flat, inter_subset_right _ _],
end

lemma flat_iff_cl_self : M.flat F ↔ M.cl F = F :=
begin
  refine ⟨λ h, subset_antisymm (sInter_subset_of_mem ⟨h, inter_subset_left F M.E⟩)
    (M.subset_cl F (flat.subset_ground h)),
    λ h, by { rw ← h, exact flat_of_cl _ _ }⟩
end

lemma flat_iff_ssubset_cl_insert_forall (hF : F ⊆ M.E . ssE) :
  M.flat F ↔ ∀ e ∈ M.E \ F, M.cl F ⊂ M.cl (insert e F) :=
begin
  refine ⟨λ h e he, (M.cl_subset (subset_insert _ _)).ssubset_of_ne _, λ h, _⟩,
  { rw [h.cl],
    refine λ h', mt ((set.ext_iff.mp h') e).mpr (not_mem_of_mem_diff he)
                    ((M.subset_cl _ _) (mem_insert _ _)),
    rw insert_eq,
    refine union_subset _ hF,
    rw singleton_subset_iff, exact he.1
  },
  rw flat_iff_cl_self,
  by_contra h',
  obtain ⟨e,he',heF⟩ := exists_of_ssubset (ssubset_of_ne_of_subset (ne.symm h') (M.subset_cl F)),
  have h'' := h e ⟨(M.cl_subset_ground F) he', heF⟩,
  rw [←(M.cl_insert_cl_eq_cl_insert e F), insert_eq_of_mem he', M.cl_cl] at h'',
  exact h''.ne rfl
end

lemma flat.cl_subset_of_subset (hF : M.flat F) (h : X ⊆ F) : M.cl X ⊆ F :=
by { have h' := M.cl_mono h, rwa hF.cl at h' }

/-- A flat is covered by another in a matroid if they are strictly nested, with no flat
  between them . -/
def covby (M : matroid_in α) (F₀ F₁ : set α) : Prop :=
  M.flat F₀ ∧ M.flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁

lemma covby_iff :
  M.covby F₀ F₁ ↔ M.flat F₀ ∧ M.flat F₁ ∧ F₀ ⊂ F₁ ∧
    ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ :=
iff.rfl

lemma covby.flat_left (h : M.covby F₀ F₁) : M.flat F₀ := h.1

lemma covby.flat_right (h : M.covby F₀ F₁) : M.flat F₁ := h.2.1

lemma covby.ssubset (h : M.covby F₀ F₁) : F₀ ⊂ F₁ := h.2.2.1

lemma covby.eq_of_ssubset_of_subset (h : M.covby F₀ F₁) (hF : M.flat F) (hF₀ : F₀ ⊂ F)
(hF₁ : F ⊆ F₁) :
  F = F₁ :=
(h.2.2.2 F hF hF₀.subset hF₁).elim (λ h', (hF₀.ne.symm h').elim) id

lemma covby.cl_insert_eq  (h : M.covby F₀ F₁) (he : e ∈ F₁ \ F₀) :
  M.cl (insert e F₀) = F₁ :=
begin
  refine h.eq_of_ssubset_of_subset (M.flat_of_cl _)
    ((ssubset_insert he.2).trans_subset (M.subset_cl _ _))
    (h.flat_right.cl_subset_of_subset (insert_subset.mpr ⟨he.1, h.ssubset.subset⟩)),
  rw [insert_eq, union_subset_iff, singleton_subset_iff],
  exact ⟨h.flat_right.subset_ground he.1, h.flat_left.subset_ground⟩
end

/-- A hyperplane is a maximal set containing no base  -/
def hyperplane (M : matroid_in α) (H : set α) : Prop := M.covby H M.E

@[ssE_finish_rules] lemma hyperplane.subset_ground (hH : M.hyperplane H) : H ⊆ M.E :=
hH.flat_left.subset_ground 

lemma hyperplane_iff_covby : M.hyperplane H ↔ M.covby H M.E := iff.rfl 

lemma hyperplane.covby (h : M.hyperplane H) : M.covby H M.E := 
h

lemma hyperplane.flat (hH : M.hyperplane H) : M.flat H :=
hH.covby.flat_left

lemma hyperplane.ssubset_ground (hH : M.hyperplane H) : H ⊂ M.E := 
hH.covby.ssubset 

lemma hyperplane.cl_insert_eq (hH : M.hyperplane H) (heH : e ∉ H) (he : e ∈ M.E . ssE) : 
  M.cl (insert e H) = M.E := 
hH.covby.cl_insert_eq ⟨he, heH⟩

lemma hyperplane.cl_eq_univ_of_ssupset (hH : M.hyperplane H) (hX : H ⊂ X)
  (hX' : X ⊆ M.E . ssE) : M.cl X = M.E :=
begin
  obtain ⟨e, heX, heH⟩ := exists_of_ssubset hX, 
  exact (M.cl_subset_ground _).antisymm ((hH.cl_insert_eq heH (hX' heX)).symm.trans_subset 
    (M.cl_subset (insert_subset.mpr ⟨heX, hX.subset⟩))),
end 

lemma hyperplane.spanning_of_ssupset (hH : M.hyperplane H) (hX : H ⊂ X) (hXE : X ⊆ M.E . ssE ) :
  M.spanning X := 
by rw [spanning_iff_cl, hH.cl_eq_univ_of_ssupset hX]

lemma hyperplane.not_spanning (hH : M.hyperplane H) : ¬M.spanning H := 
by { rw hH.flat.spanning_iff, exact hH.ssubset_ground.ne }

lemma hyperplane_iff_maximal_nonspanning : 
  M.hyperplane H ↔ H ∈ maximals (⊆) {X | X ⊆ M.E ∧ ¬ M.spanning X } :=
begin
  simp_rw [mem_maximals_set_of_iff, and_imp],  
  refine ⟨λ h, ⟨⟨h.subset_ground, h.not_spanning⟩, λ X hX hX' hHX, _⟩, λ h, _⟩,
  { exact by_contra (λ hne, hX' (h.spanning_of_ssupset (hHX.ssubset_of_ne hne))) },
  rw [hyperplane_iff_covby, covby_iff, and_iff_right M.ground_flat, 
    flat_iff_ssubset_cl_insert_forall h.1.1],   
  refine ⟨λ e he, _, h.1.1.ssubset_of_ne (by { rintro rfl, exact h.1.2 M.ground_spanning }), 
    λ F hF hHF hFE, or_iff_not_imp_right.mpr (λ hFE', _)⟩, 
  { have h' := h.2 (insert_subset.mpr ⟨he.1, h.1.1⟩), 
    simp_rw [subset_insert, forall_true_left, @eq_comm _  H, insert_eq_self, 
      iff_false_intro he.2, imp_false, not_not, spanning_iff_cl] at h', 
    rw [h', ←not_spanning_iff_cl h.1.1], 
    exact h.1.2 },
  have h' := h.2 hFE, 
  rw [hF.spanning_iff] at h', 
  rw [h' hFE' hHF], 
end 

@[simp] lemma compl_cocircuit_iff_hyperplane (hH : H ⊆ M.E . ssE) : 
  M.cocircuit (M.E \ H) ↔ M.hyperplane H :=
begin
  simp_rw [cocircuit_iff_mem_minimals_compl_nonspanning, hyperplane_iff_maximal_nonspanning, 
    mem_maximals_set_of_iff, mem_minimals_set_of_iff, sdiff_sdiff_right_self, inf_eq_inter, 
    ground_inter_right, and_imp, and_iff_right hH, and.congr_right_iff, subset_diff], 
  refine λ hH', ⟨λ h X hX hXE hXH, _, λ h X hX hXE , _⟩, 
  { rw ←diff_eq_diff_iff_eq (hXH.trans hX) hX, 
    exact @h (M.E \ X) (by simpa) ⟨(diff_subset _ _), 
      disjoint_of_subset_right hXH disjoint_sdiff_left⟩ },
  rw [@h (M.E \ X) (diff_subset _ _) hX, sdiff_sdiff_right_self, inf_eq_inter, 
    inter_eq_self_of_subset_right hXE.1], 
  rw [subset_diff, and_iff_right hH],
  exact hXE.2.symm,  
end

@[simp] lemma compl_hyperplane_iff_cocircuit (h : K ⊆ M.E . ssE ) :
  M.hyperplane (M.E \ K) ↔ M.cocircuit K := 
by rw [←compl_cocircuit_iff_hyperplane, diff_diff_right, diff_self, empty_union,
  inter_comm, (inter_eq_left_iff_subset.mpr h)]

end flat

section loop -- taken from loop.lean

variables {α : Type*} {M M₁ M₂ : matroid_in α} {I C X Y Z K F F₁ F₂ : set α} {e f x y z : α}

/-- A loop is a member of the closure of the empty set -/
def loop (M : matroid_in α) (e : α) : Prop := e ∈ M.cl ∅

lemma loop_iff_mem_cl_empty : M.loop e ↔ e ∈ M.cl ∅ := iff.rfl 

@[ssE_finish_rules] lemma loop.mem_ground (he : M.loop e) : e ∈ M.E := cl_subset_ground M ∅ he

lemma loop_iff_dep : M.loop e ↔ M.dep {e} := 
by rw [loop_iff_mem_cl_empty, 
  M.empty_indep.mem_cl_iff_of_not_mem (not_mem_empty e), insert_emptyc_eq]

lemma loop.dep (he : M.loop e) : M.dep {e} :=
loop_iff_dep.mp he

lemma loop_iff_circuit : M.loop e ↔ M.circuit {e} := 
begin
  by_cases he : e ∈ M.E, 
  { simp_rw [circuit_iff_forall_ssubset, ssubset_singleton_iff, forall_eq, empty_indep, and_true, 
      loop_iff_dep] }, 
  exact iff_of_false (he ∘ loop.mem_ground) (he ∘ (λ h, h.subset_ground rfl)),   
end 

lemma loop.not_indep_of_mem (he : M.loop e) (h : e ∈ X) : ¬ M.indep X := 
λ hX, he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

lemma loop.not_mem_of_indep (he : M.loop e) (hI : M.indep I) : e ∉ I :=
λ h, he.not_indep_of_mem h hI

lemma loop_iff_not_indep (he : e ∈ M.E . ssE) : M.loop e ↔ ¬ M.indep {e} := 
by rw [loop_iff_dep, ←not_indep_iff]

/- ### Nonloops -/

/-- A `nonloop` is an element that is not a loop -/
def nonloop (M : matroid_in α) (e : α) : Prop := ¬ M.loop e ∧ e ∈ M.E 

@[ssE_finish_rules] lemma nonloop.mem_ground (h : M.nonloop e) : e ∈ M.E := h.2 

lemma nonloop.not_loop (he : M.nonloop e) : ¬ M.loop e :=
he.1

lemma loop.not_nonloop (he : M.loop e) : ¬ M.nonloop e := 
λ h, h.not_loop he

@[simp] lemma not_loop_iff (he : e ∈ M.E . ssE) : ¬ M.loop e ↔ M.nonloop e := 
(and_iff_left he).symm

@[simp] lemma not_nonloop_iff (he : e ∈ M.E . ssE) : ¬ M.nonloop e ↔ M.loop e := 
by rw [←not_loop_iff, not_not]

@[simp] lemma indep_singleton : M.indep {e} ↔ M.nonloop e := 
begin
  rw [nonloop, loop_iff_dep, dep_iff, not_and, not_imp_not, singleton_subset_iff],  
  exact ⟨λ h, ⟨λ _, h, singleton_subset_iff.mp h.subset_ground⟩, λ h, h.1 h.2⟩,
end

alias indep_singleton ↔ indep.nonloop nonloop.indep

attribute [protected] indep.nonloop nonloop.indep

lemma indep.nonloop_of_mem (hI : M.indep I) (h : e ∈ I) : M.nonloop e := 
by { rw [←not_loop_iff], exact λ he, (he.not_mem_of_indep hI) h }

lemma cocircuit.nonloop_of_mem {K : set α} (hK : M.cocircuit K) (he : e ∈ K) : M.nonloop e := 
begin
  have heE : e ∈ M.E := hK.subset_ground he,
  rw [←not_loop_iff], 
  intro hel, 
  rw [cocircuit_iff_mem_minimals, mem_minimals_set_of_iff] at hK, 
  suffices : K = K \ {e}, from (this.subset he).2 rfl, 
  apply hK.2 (λ B hB, _) (diff_subset _ _), 
  rw [diff_eq, inter_right_comm, inter_assoc, ←diff_eq, 
    diff_singleton_eq_self (hel.not_mem_of_indep hB.indep)], 
  exact hK.1 B hB, 
end 

/- ### Coloops -/ 

/-- A coloop is a loop of the dual  -/
def coloop (M : matroid_in α) (e : α) : Prop := M﹡.loop e   

@[ssE_finish_rules] lemma coloop.mem_ground (he : M.coloop e) : e ∈ M.E :=
@loop.mem_ground α M﹡ e he 

lemma coloop_iff_mem_cl_empty : M.coloop e ↔ e ∈ M﹡.cl ∅ := iff.rfl    

lemma coloop.dual_loop (he : M.coloop e) : M﹡.loop e := he 

lemma loop.dual_coloop (he : M.loop e) : M﹡.coloop e := by rwa [coloop, dual_dual]

@[simp] lemma dual_loop_iff_coloop : M﹡.loop e ↔ M.coloop e :=
⟨λ h, by {rw ←dual_dual M, exact h.dual_coloop}, coloop.dual_loop⟩

lemma loop_iff_not_mem_base_forall (he : e ∈ M.E . ssE) : M.loop e ↔ ∀ B, M.base B → e ∉ B :=
by simp_rw [loop_iff_dep, ←not_indep_iff, indep_iff_subset_base, not_exists, 
  not_and, singleton_subset_iff]

lemma coloop_iff_forall_mem_base : M.coloop e ↔ ∀ ⦃B⦄, M.base B → e ∈ B := 
begin
  obtain (he | he) := (em (e ∈ M.E)).symm, 
  { refine iff_of_false (he ∘ coloop.mem_ground) (he ∘ (λ h, _)),
    obtain ⟨B, hB⟩ := M.exists_base, 
    exact hB.subset_ground (h hB) },
  rw [←dual_loop_iff_coloop, loop_iff_not_mem_base_forall], 
  simp_rw [dual_base_iff'], 
  refine ⟨λ h B hB, _, λ h B hB heB, (h hB.1).2 heB⟩,
  have he' := h (M.E \ B) ⟨_, diff_subset _ _⟩,  
  { simp only [mem_diff, not_and, not_not_mem] at he', exact he' he },
  simp only [sdiff_sdiff_right_self, inf_eq_inter],
  rwa inter_eq_self_of_subset_right hB.subset_ground,
end 

lemma coloop.mem_of_base (he : M.coloop e) {B : set α} (hB : M.base B) : e ∈ B :=
coloop_iff_forall_mem_base.mp he hB 

lemma coloop_iff_forall_mem_cl_iff_mem (he : e ∈ M.E . ssE) : 
  M.coloop e ↔ ∀ X, e ∈ M.cl X ↔ e ∈ X :=
begin
  rw coloop_iff_forall_mem_base, 
  refine ⟨λ h X, _, λ h B hB, (h B).mp (by rwa hB.cl)⟩,
  rw [cl_eq_cl_inter_ground], 
  refine ⟨λ hecl, _, λ heX, _⟩, 
  { obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
    obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_supset, 
    have heB := h hB, 
    rw [hI.mem_cl_iff, imp_iff_right (hB.indep.subset (insert_subset.mpr ⟨heB, hIB⟩))] at hecl, 
    exact (hI.subset hecl).1 },  
  exact mem_cl_of_mem' _ ⟨heX, he⟩, 
end 

lemma coloop.mem_cl_iff_mem (he : M.coloop e) : e ∈ M.cl X ↔ e ∈ X :=
coloop_iff_forall_mem_cl_iff_mem.mp he X

lemma coloop.insert_indep_of_indep (he : M.coloop e) (hI : M.indep I) : M.indep (insert e I) :=
(em (e ∈ I)).elim (λ h, by rwa insert_eq_of_mem h) 
  (λ h, by rwa [hI.insert_indep_iff_of_not_mem h, he.mem_cl_iff_mem])  

lemma union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.indep (I ∪ K) ↔ M.indep I :=
begin
  refine ⟨λ h, h.subset (subset_union_left I K), λ h, _⟩,
  obtain ⟨B, hB, hIB⟩ := h.exists_base_supset, 
  exact hB.indep.subset (union_subset hIB (hK.trans (λ e he, coloop.mem_of_base he hB))), 
end 

lemma diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.indep (I \ K) ↔ M.indep I :=
by rw [←union_indep_iff_indep_of_subset_coloops hK, diff_union_self, 
  union_indep_iff_indep_of_subset_coloops hK]

lemma indep_iff_diff_coloops_indep : M.indep I ↔ M.indep (I \ M﹡.cl ∅) := 
  (diff_indep_iff_indep_of_subset_coloops subset.rfl).symm 

lemma coloops_indep (M : matroid_in α) : M.indep (M﹡.cl ∅) := 
by { rw [indep_iff_diff_coloops_indep, diff_self], exact M.empty_indep }

lemma indep_of_subset_coloops (h : I ⊆ M﹡.cl ∅) : M.indep I := 
M.coloops_indep.subset h

lemma coloop_iff_cocircuit : M.coloop e ↔ M.cocircuit {e} := 
by rw [←dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit]

end loop

section rank -- taken from rank.lean

variables {α : Type*} {M : matroid_in α}  {B X Y X' Y' Z I J : set α} {e f x y z : α} {k n : ℕ}

/-- The rank `r X` of a set `X` is the cardinality of one of its bases, or zero if its bases are 
  infinite -/
def er {α : Type*} (M : matroid_in α) (X : set α) : ℕ∞ :=
  ⨅ (I : {I | M.basis I (X ∩ M.E)}), encard (I : set α)

lemma basis.encard_of_inter_ground (hI : M.basis I (X ∩ M.E)) : I.encard = M.er X :=
begin
  have hrw : ∀ J : {J : set α | M.basis J (X ∩ M.E)}, (J : set α).encard = I.encard,
  { rintro ⟨J, hJ⟩, exact (hI.encard_eq_encard_of_basis hJ).symm },
  haveI : nonempty {J : set α | M.basis J (X ∩ M.E)}, 
    from let ⟨I,hI⟩ := M.exists_basis (X ∩ M.E) in ⟨⟨I,hI⟩⟩,
  simp_rw [er, hrw, cinfi_const], 
end 

lemma basis.encard (hI : M.basis I X) : I.encard = M.er X := 
hI.basis_inter_ground.encard_of_inter_ground 

lemma eq_er_iff {n : ℕ∞} (hX : X ⊆ M.E . ssE) : M.er X = n ↔ ∃ I, M.basis I X ∧ I.encard = n :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.encard], 
  refine ⟨λ h, ⟨I, hI, h⟩, _⟩,
  rintro ⟨J, hJ, rfl⟩, 
  rw [hI.encard, hJ.encard], 
end  

lemma indep.er (hI : M.indep I) : M.er I = I.encard := eq_er_iff.mpr ⟨I, hI.basis_self, rfl⟩

lemma basis.er (hIX : M.basis I X) : M.er I = M.er X := 
by rw [←hIX.encard, hIX.indep.er]

lemma er_eq_er_inter_ground (M : matroid_in α) (X : set α) : M.er X = M.er (X ∩ M.E) :=
by { obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), rwa [←hI.encard_of_inter_ground, ←basis.encard] }

lemma er_mono (M : matroid_in α) : monotone M.er := 
begin
  rintro X Y (h : X ⊆ Y), 
  rw [er_eq_er_inter_ground, M.er_eq_er_inter_ground Y], 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  obtain ⟨J, hJ, hIJ⟩ :=
    hI.indep.subset_basis_of_subset (hI.subset.trans (inter_subset_inter_left M.E h)), 
  rw [←hI.encard, ←hJ.encard], 
  exact encard_mono hIJ,
end 

lemma indep.encard_le_er_of_subset (hI : M.indep I) (hIX : I ⊆ X) : I.encard ≤ M.er X :=
  by { rw [←hI.er], exact M.er_mono hIX }

lemma er_le_iff {n : ℕ∞} : M.er X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.encard ≤ n) :=
begin
  refine ⟨λ h I hIX hI, (hI.encard_le_er_of_subset hIX).trans h, λ h, _⟩,
  obtain ⟨J, hJ⟩ := M.exists_basis (X ∩ M.E), 
  rw [er_eq_er_inter_ground, ←hJ.encard], 
  exact h J (hJ.subset.trans (inter_subset_left _ _)) hJ.indep, 
end 

@[simp] lemma er_cl (M : matroid_in α) (X : set α) : M.er (M.cl X) = M.er X :=
begin
  rw [cl_eq_cl_inter_ground, M.er_eq_er_inter_ground X], 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw [←hI.er, ←hI.cl, hI.indep.basis_cl.er], 
end 

lemma basis_iff_indep_encard_eq_of_finite (hIfin : I.finite) (hXE : X ⊆ M.E . ssE) :
  M.basis I X ↔ I ⊆ X ∧ M.indep I ∧ I.encard = M.er X :=
begin
  rw [basis_iff_indep_cl, and_comm (I ⊆ X), ←and_assoc, and.congr_left_iff, and.congr_right_iff], 
  refine λ hIX hI, ⟨λ h, (hI.encard_le_er_of_subset hIX).antisymm _, λ h, _⟩, 
  { refine (M.er_mono h).trans _, 
    rw [er_cl, hI.er], exact rfl.le }, 
  intros e he, 
  rw [hI.mem_cl_iff (hXE he)], 
  refine λ hi, by_contra (λ he', _), 
  have hr := hi.er, rw [encard_insert_of_not_mem he'] at hr, 
  have hle := M.er_mono (insert_subset.mpr ⟨he, hIX⟩), 
  rw [hr, ←h, hIfin.encard_eq, ←nat.cast_one, ←nat.cast_add, nat.cast_le] at hle, 
  simpa using hle, 
end  

def r_fin (M : matroid_in α) (X : set α) := M.er X < ⊤ 

lemma r_fin_iff_er_ne_top : M.r_fin X ↔ M.er X ≠ ⊤ := 
by rw [r_fin, ←lt_top_iff_ne_top]

lemma r_fin_iff_er_lt_top : M.r_fin X ↔ M.er X < ⊤ := 
iff.rfl 

lemma r_fin_iff_inter_ground : M.r_fin X ↔ M.r_fin (X ∩ M.E) := 
by rw [r_fin, er_eq_er_inter_ground, r_fin]

lemma to_r_fin (M : matroid_in α) [finite_rk M] (X : set α) : M.r_fin X :=  
begin
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw [r_fin_iff_inter_ground, r_fin_iff_er_lt_top, ← hI.encard, encard_lt_top_iff_finite], 
  exact hI.finite, 
end

/-- The rank function. Intended to be used in a `finite_rk` matroid; otherwise `er` is better.-/
def r (M : matroid_in α) (X : set α) : ℕ := (M.er X).to_nat 

/-- The rank of the ground set of a matroid -/
@[reducible] def rk (M : matroid_in α) : ℕ := M.r M.E 

lemma rk_def (M : matroid_in α) : M.rk = M.r M.E := rfl 

@[simp] lemma er_to_nat_eq_r (M : matroid_in α) (X : set α) : (M.er X).to_nat = M.r X := rfl 

lemma r_fin.coe_r_eq_er (hX : M.r_fin X) : (M.r X : ℕ∞) = M.er X :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rwa [r, er_eq_er_inter_ground, ←hI.encard, enat.coe_to_nat_eq_self, hI.encard, 
    ←er_eq_er_inter_ground, ←r_fin_iff_er_ne_top],  
end 

@[simp] lemma coe_r_eq_er (M : matroid_in α) [finite_rk M] (X : set α) : (M.r X : ℕ∞) = M.er X :=
(M.to_r_fin X).coe_r_eq_er

@[simp] lemma er_eq_coe_iff [finite_rk M] {n : ℕ} : M.er X = n ↔ M.r X = n := 
by rw [←coe_r_eq_er, enat.coe_inj]

@[simp] lemma er_le_er_iff [finite_rk M] : M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := 
by rw [←coe_r_eq_er, ←coe_r_eq_er, enat.coe_le_coe_iff]

lemma indep.r (hI : M.indep I) : M.r I = I.ncard := 
by rw [←er_to_nat_eq_r, hI.er, encard_to_nat_eq]

lemma basis_iff_indep_card [finite_rk M] (hX : X ⊆ M.E . ssE) : 
  M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.ncard = M.r X :=
begin
  refine I.finite_or_infinite.symm.elim (λ hI, iff_of_false (hI ∘ (λ h, h.indep.finite)) 
    (hI ∘ λ h, h.1.finite)) (λ hIfin, _), 
  rw [basis_iff_indep_encard_eq_of_finite hIfin hX, and_comm (_ ⊆ _), and_assoc,  
    and_comm (_ ⊆ _),  ←coe_r_eq_er, hIfin.encard_eq, enat.coe_inj], 
end 

lemma base_iff_indep_card [finite_rk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
by rw [base_iff_basis_ground, basis_iff_indep_card, ←and_assoc, 
  and_iff_left_of_imp indep.subset_ground]

lemma r_eq_r_inter_ground (M : matroid_in α) (X : set α) : M.r X = M.r (X ∩ M.E) :=
by rw [←er_to_nat_eq_r, er_eq_er_inter_ground, er_to_nat_eq_r]

lemma r_le_iff [finite_rk M] : M.r X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.ncard ≤ n) :=
begin
  simp_rw [←enat.coe_le_coe_iff, coe_r_eq_er, er_le_iff, encard_le_coe_iff, enat.coe_le_coe_iff], 
  exact forall_congr (λ I, ⟨by tauto, λ h hIX hI, ⟨hI.finite, h hIX hI⟩⟩), 
end 

lemma r_mono (M : matroid_in α) [finite_rk M] : monotone M.r :=
by { rintro X Y (hXY : X ⊆ Y), rw [←er_le_er_iff],  exact M.er_mono hXY }

lemma r_le_card (M : matroid_in α) [finite M] (X : set α) (hX : X ⊆ M.E . ssE) : M.r X ≤ X.ncard := 
by { rw [r_le_iff], exact λ I h _, ncard_le_of_subset h (M.set_finite X) }  

lemma r_le_rk (M : matroid_in α) [finite_rk M] (X : set α) : M.r X ≤ M.rk := 
by { rw [r_eq_r_inter_ground], exact M.r_mono (inter_subset_right _ _) }

lemma indep.base_of_rk_le_card [finite_rk M] (hI : M.indep I) (h : M.rk ≤ I.ncard) : M.base I :=
base_iff_indep_card.mpr ⟨hI, h.antisymm' (by {rw ←hI.r, apply r_le_rk})⟩

lemma basis.card (h : M.basis I X) : I.ncard = M.r X := 
by rw [←encard_to_nat_eq, ←er_to_nat_eq_r, h.encard]

lemma base.card (hB : M.base B) : B.ncard = M.rk := 
by rw [(base_iff_basis_ground.mp hB).card, rk]

end rank

section simple -- taken from simple.lean

variables {α : Type*} {N M : matroid_in α} {e f g : α} {X Y Z S T : set α}

/-- A matroid_in is loopless on a set if that set doesn't contain a loop. -/
def loopless_on (M : matroid_in α) (X : set α) : Prop := ∀ ⦃e⦄, e ∈ X → M.nonloop e

/-- A matroid_in is loopless if it has no loop -/
def loopless (M : matroid_in α) : Prop := ∀ e ∈ M.E, M.nonloop e

@[simp] lemma loopless_on_ground : M.loopless_on M.E ↔ M.loopless := by simp [loopless_on, loopless]

/-- the property of a set containing no loops or para pairs -/
def simple_on (M : matroid_in α) (X : set α) : Prop := ∀ ⦃e⦄, e ∈ X → ∀ ⦃f⦄, f ∈ X → M.indep {e, f}

/-- the property of a matroid_in having no loops or para pairs -/
def simple (M : matroid_in α) : Prop := ∀ (e ∈ M.E) (f ∈ M.E), M.indep {e, f}

@[simp] lemma simple_on_ground : M.simple_on M.E ↔ M.simple := by simp [simple_on, simple]

protected lemma simple_on.loopless_on (h : M.simple_on X) : M.loopless_on X :=
begin
  intros x hx,
  rw [←indep_singleton , ←pair_eq_singleton],
  exact h hx hx,
end

protected lemma simple.loopless (h : M.simple) : M.loopless :=
  loopless_on_ground.2 ((simple_on_ground.2 h).loopless_on)

end simple

end matroid_in