import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_218

private def mono {n : ℕ} (φ : DMFormula n) : Prop :=
  DMFormula.rec (motive := fun _ : DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true)
    (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

private def center (b : ℕ) : Fin (2 * b + 1) := ⟨0, by omega⟩

private def endpoint {b : ℕ} (i : Fin b) (p : Bool) : Fin (2 * b + 1) :=
  ⟨2 * i.val + (if p then 1 else 2), by have := i.isLt; cases p <;> simp <;> omega⟩

private lemma endpoint_inj {b : ℕ} {i j : Fin b} {p r : Bool}
    (h : endpoint i p = endpoint j r) : i = j ∧ p = r := by
  have h' := congrArg Fin.val h
  cases p <;> cases r <;> simp [endpoint] at h' ⊢ <;>
    first | exact Fin.ext (by omega) | omega

private lemma endpoint_ne_center {b : ℕ} (i : Fin b) (p : Bool) :
    endpoint i p ≠ center b := by
  intro h
  have he := congrArg Fin.val h
  cases p <;> simp [endpoint, center] at he

private lemma vertices {b : ℕ} (u : Fin (2 * b + 1)) :
    u = center b ∨ ∃ (i : Fin b) (p : Bool), u = endpoint i p := by
  by_cases hu : u.val = 0
  · exact Or.inl (Fin.ext hu)
  · have hlt := u.isLt
    let i : Fin b := ⟨(u.val - 1) / 2, by omega⟩
    refine Or.inr ⟨i, decide (u.val % 2 = 1), Fin.ext ?_⟩
    by_cases h : u.val % 2 = 1 <;> simp [i, endpoint, h] <;> omega

private def target {b : ℕ} (x : Fin (2 * b + 1) → Bool) : Prop :=
  ∃ u v : Fin (2 * b + 1),
    ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧
      x u = true ∧ x v = true

private lemma target_iff {b : ℕ} (x : Fin (2 * b + 1) → Bool) :
    target x ↔
      (x (center b) = true ∧ ∃ (i : Fin b) (p : Bool), x (endpoint i p) = true) ∨
        (∃ i : Fin b, x (endpoint i true) = true ∧ x (endpoint i false) = true) := by
  constructor
  · rintro ⟨u, v, he | he, hu, hv⟩
    · left
      obtain rfl : u = center b := Fin.ext he.1
      rcases vertices v with rfl | ⟨i, p, rfl⟩
      · exact (Nat.lt_irrefl 0 he.2).elim
      · exact ⟨hu, i, p, hv⟩
    · right
      have hlt := v.isLt
      let i : Fin b := ⟨u.val / 2, by have := he.2; omega⟩
      have hua : u = endpoint i true := Fin.ext (by simp [endpoint, i]; omega)
      have hva : v = endpoint i false := Fin.ext (by simp [endpoint, i]; omega)
      exact ⟨i, hua ▸ hu, hva ▸ hv⟩
  · rintro (⟨h0, i, p, hp⟩ | ⟨i, h1, h2⟩)
    · exact ⟨center b, endpoint i p, Or.inl ⟨rfl, by cases p <;> simp [endpoint] <;> omega⟩, h0, hp⟩
    · exact ⟨endpoint i true, endpoint i false, Or.inr (by simp [endpoint]), h1, h2⟩

private def allOr {n : ℕ} : (k : ℕ) → (Fin (k+1) → DMFormula n) → DMFormula n
  | 0, f => f 0
  | k+1, f => .or (f 0) (allOr k (fun i => f i.succ))

private lemma allOr_eval {n : ℕ} (k : ℕ) (f : Fin (k+1) → DMFormula n) (x : Fin n → Bool) :
    (allOr k f).eval x = true ↔ ∃ i, (f i).eval x = true := by
  induction k with
  | zero => simp [allOr, Fin.exists_fin_one]
  | succ k ih =>
    simp only [allOr, DMFormula.eval, Bool.or_eq_true, ih, Fin.exists_fin_succ]

private lemma allOr_mono {n : ℕ} (k : ℕ) (f : Fin (k+1) → DMFormula n)
    (h : ∀ i, mono (f i)) : mono (allOr k f) := by
  induction k with
  | zero => exact h 0
  | succ k ih => exact ⟨h 0, ih _ (fun i => h i.succ)⟩

private lemma allOr_leaves {n : ℕ} (k : ℕ) (f : Fin (k+1) → DMFormula n) (c : ℕ)
    (h : ∀ i, (f i).leaves = c) : (allOr k f).leaves = (k+1) * c := by
  induction k with
  | zero => simpa [allOr] using h 0
  | succ k ih =>
    simp [allOr, DMFormula.leaves, h, ih _ (fun i => h i.succ), Nat.add_mul, Nat.add_comm]

private lemma construction (b : ℕ) (hb : 1 ≤ b) :
    ∃ φ : DMFormula (2 * b + 1), φ.leaves = 4*b+1 ∧ mono φ ∧
      ∀ x, φ.eval x = true ↔ target x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  let lit := fun i : Fin (2 * (k+1) + 1) => DMFormula.lit i true
  let arms := fun i : Fin (k+1) => DMFormula.or (lit (endpoint i true)) (lit (endpoint i false))
  let rims := fun i : Fin (k+1) => DMFormula.and (lit (endpoint i true)) (lit (endpoint i false))
  refine ⟨.or (.and (lit (center (k+1))) (allOr k arms)) (allOr k rims), ?_, ?_, ?_⟩
  · change 1 + (allOr k arms).leaves + (allOr k rims).leaves = _
    rw [allOr_leaves k arms 2 (fun _ => rfl), allOr_leaves k rims 2 (fun _ => rfl)]
    omega
  · exact ⟨⟨rfl, allOr_mono k arms (fun _ => ⟨rfl, rfl⟩)⟩,
      allOr_mono k rims (fun _ => ⟨rfl, rfl⟩)⟩
  · intro x
    simp only [DMFormula.eval, Bool.or_eq_true, Bool.and_eq_true, allOr_eval,
      arms, rims, lit, ite_true, target_iff]
    have hArm (i : Fin (k+1)) :
        (x (endpoint i true) = true ∨ x (endpoint i false) = true) ↔
          ∃ p, x (endpoint i p) = true := by
      constructor
      · rintro (h | h)
        · exact ⟨true, h⟩
        · exact ⟨false, h⟩
      · rintro ⟨p, h⟩
        cases p
        · exact Or.inr h
        · exact Or.inl h
    simp only [hArm]

-- The rectangle-counting argument is due to Daniel de Vries, pull request 1822.
private def leafLabel {n : ℕ} : DMFormula n → ℕ → Fin n
  | .lit i _, _ => i
  | .and l r, j | .or l r, j =>
    if j < l.leaves then leafLabel l j else leafLabel r (j - l.leaves)

private def owner {n : ℕ} : DMFormula n → (Fin n → Bool) → (Fin n → Bool) → ℕ
  | .lit _ _, _, _ => 0
  | .and l r, x, y => if l.eval y then l.leaves + owner r x y else owner l x y
  | .or l r, x, y => if l.eval x then owner l x y else l.leaves + owner r x y

private lemma owner_valid {n : ℕ} (φ : DMFormula n) (hm : mono φ)
    (x y : Fin n → Bool) (hx : φ.eval x = true) (hy : φ.eval y = false) :
    owner φ x y < φ.leaves ∧
      x (leafLabel φ (owner φ x y)) = true ∧ y (leafLabel φ (owner φ x y)) = false := by
  induction φ with
  | lit i p =>
    change p = true at hm
    subst p
    exact ⟨Nat.zero_lt_succ 0, hx, hy⟩
  | and l r ihl ihr =>
    change mono l ∧ mono r at hm
    simp only [DMFormula.eval, Bool.and_eq_true] at hx
    cases h : l.eval y with
    | false =>
      have hL := ihl hm.1 hx.1 h
      simp [owner, leafLabel, DMFormula.leaves, h, hL.1, hL.2, hL.1.trans_le (Nat.le_add_right _ _)]
    | true =>
      have hR := ihr hm.2 hx.2 (by simpa [DMFormula.eval, h] using hy)
      have hn : ¬ l.leaves + owner r x y < l.leaves := by omega
      simp [owner, leafLabel, DMFormula.leaves, h, hn, hR.1, hR.2]
  | or l r ihl ihr =>
    change mono l ∧ mono r at hm
    simp only [DMFormula.eval, Bool.or_eq_false_iff] at hy
    cases h : l.eval x with
    | true =>
      have hL := ihl hm.1 h hy.1
      simp [owner, leafLabel, DMFormula.leaves, h, hL.1, hL.2, hL.1.trans_le (Nat.le_add_right _ _)]
    | false =>
      have hR := ihr hm.2 (by simpa [DMFormula.eval, h] using hx) hy.2
      have hn : ¬ l.leaves + owner r x y < l.leaves := by omega
      simp [owner, leafLabel, DMFormula.leaves, h, hn, hR.1, hR.2]

private lemma owner_cross {n : ℕ} (φ : DMFormula n) (hm : mono φ)
    (x y x' y' : Fin n → Bool)
    (hx : φ.eval x = true) (hy : φ.eval y = false)
    (hx' : φ.eval x' = true) (hy' : φ.eval y' = false)
    (he : owner φ x y = owner φ x' y') :
    owner φ x y' = owner φ x y := by
  induction φ generalizing x y x' y' with
  | lit i p => rfl
  | and l r ihl ihr =>
    change mono l ∧ mono r at hm
    simp only [DMFormula.eval, Bool.and_eq_true] at hx hx'
    cases h : l.eval y <;> cases h' : l.eval y' <;> simp only [owner, h, h', Bool.false_eq_true,
      ↓reduceIte] at he ⊢
    · exact ihl hm.1 x y x' y' hx.1 h hx'.1 h' he
    · have hL := (owner_valid l hm.1 x y hx.1 h).1
      omega
    · have hL := (owner_valid l hm.1 x' y' hx'.1 h').1
      omega
    · have hR : r.eval y = false := by simpa [DMFormula.eval, h] using hy
      have hR' : r.eval y' = false := by simpa [DMFormula.eval, h'] using hy'
      rw [ihr hm.2 x y x' y' hx.2 hR hx'.2 hR' (by omega)]
  | or l r ihl ihr =>
    change mono l ∧ mono r at hm
    simp only [DMFormula.eval, Bool.or_eq_false_iff] at hy hy'
    cases h : l.eval x <;> cases h' : l.eval x' <;> simp only [owner, h, h', Bool.false_eq_true,
      ↓reduceIte] at he ⊢
    · have hR : r.eval x = true := by simpa [DMFormula.eval, h] using hx
      have hR' : r.eval x' = true := by simpa [DMFormula.eval, h'] using hx'
      rw [ihr hm.2 x y x' y' hR hy.2 hR' hy'.2 (by omega)]
    · have hL := (owner_valid l hm.1 x' y' h' hy'.1).1
      omega
    · have hL := (owner_valid l hm.1 x y h hy.1).1
      omega
    · exact ihl hm.1 x y x' y' h hy.1 h' hy'.1 he

private def spoke {b : ℕ} (i : Fin b) (p : Bool) (v : Fin (2*b+1)) : Bool :=
  decide (v = center b ∨ v = endpoint i p)

private def rim {b : ℕ} (i : Fin b) (v : Fin (2*b+1)) : Bool :=
  decide (v = endpoint i true ∨ v = endpoint i false)

private def transversal {b : ℕ} (c : Fin b → Bool) (v : Fin (2*b+1)) : Bool :=
  decide (∃ i : Fin b, v = endpoint i (c i))

private def hubOnly (b : ℕ) (v : Fin (2*b+1)) : Bool := decide (v = center b)

private lemma trans_ep {b : ℕ} (c : Fin b → Bool) (i : Fin b) (p : Bool) :
    transversal c (endpoint i p) = true ↔ p = c i := by
  simp only [transversal, decide_eq_true_eq]
  constructor
  · rintro ⟨j, h⟩
    obtain ⟨rfl, hp⟩ := endpoint_inj h
    exact hp
  · intro hp
    exact ⟨i, congrArg (endpoint i) hp⟩

private lemma trans_hub {b : ℕ} (c : Fin b → Bool) :
    transversal c (center b) = false := by
  simp [transversal, fun i => (endpoint_ne_center i (c i)).symm]

private lemma spoke_target {b : ℕ} (i : Fin b) (p : Bool) : target (spoke i p) := by
  exact (target_iff _).mpr (Or.inl ⟨by simp [spoke], i, p, by simp [spoke]⟩)

private lemma rim_target {b : ℕ} (i : Fin b) : target (rim i) := by
  exact (target_iff _).mpr (Or.inr ⟨i, by simp [rim], by simp [rim]⟩)

private lemma trans_target {b : ℕ} (c : Fin b → Bool) : ¬ target (transversal c) := by
  rw [target_iff]
  rintro (⟨hc, _⟩ | ⟨i, h1, h2⟩)
  · exact Bool.false_ne_true ((trans_hub c).symm.trans hc)
  · have h1' := (trans_ep c i true).mp h1
    have h2' := (trans_ep c i false).mp h2
    exact (by decide : true ≠ false) (h1'.trans h2'.symm)

private lemma hub_target (b : ℕ) : ¬ target (hubOnly b) := by
  rw [target_iff]
  simp [hubOnly, endpoint_ne_center]


private lemma distinct_label {J V : Type} (label : J → V) {a b : J}
    (h : label a ≠ label b) : a ≠ b := fun he => h (congrArg label he)

private lemma leaf_bounds {b : ℕ} (hb : 1 ≤ b) (φ : DMFormula (2*b+1)) (hm : mono φ)
    (hf : ∀ x, φ.eval x = true ↔ target x) : 4*b+1 ≤ φ.leaves := by
  classical
  have hFalse (y) (hy : ¬ target y) : φ.eval y = false :=
    Bool.eq_false_iff.mpr (fun he => hy ((hf y).mp he))
  let label (l : Fin φ.leaves) := leafLabel φ l.val
  let route (x y : Fin (2*b+1) → Bool) (hx : target x) (hy : ¬ target y) : Fin φ.leaves :=
    ⟨owner φ x y, (owner_valid φ hm x y ((hf x).mpr hx) (hFalse y hy)).1⟩
  have valid (x y) (hx : target x) (hy : ¬ target y) :
      x (label (route x y hx hy)) = true ∧ y (label (route x y hx hy)) = false :=
    (owner_valid φ hm x y ((hf x).mpr hx) (hFalse y hy)).2
  have cross (x y z w) (hx : target x) (hy : ¬ target y)
      (hz : target z) (hw : ¬ target w)
      (h : route x y hx hy = route z w hz hw) :
      route x w hx hw = route x y hx hy :=
    Fin.ext (owner_cross φ hm x y z w ((hf x).mpr hx) (hFalse y hy)
      ((hf z).mpr hz) (hFalse w hw) (congrArg Fin.val h))
  let R (i : Fin b) (p : Bool) :=
    route (spoke i p) (hubOnly b) (spoke_target i p) (hub_target b)
  let D (i : Fin b) (c : Fin b → Bool) :=
    route (rim i) (transversal c) (rim_target i) (trans_target c)
  let W (i : Fin b) (p : Bool) (c : Fin b → Bool) :=
    route (spoke i p) (transversal c) (spoke_target i p) (trans_target c)
  have rlab (i : Fin b) (p : Bool) : label (R i p) = endpoint i p := by
    obtain ⟨h1, h2⟩ := valid (spoke i p) (hubOnly b) (spoke_target i p) (hub_target b)
    change spoke i p (label (R i p)) = true at h1
    change hubOnly b (label (R i p)) = false at h2
    simp [hubOnly] at h2
    simpa [spoke, h2] using h1
  have dlab (i : Fin b) (c : Fin b → Bool) : label (D i c) = endpoint i (!(c i)) := by
    obtain ⟨h1, h2⟩ := valid (rim i) (transversal c) (rim_target i) (trans_target c)
    change rim i (label (D i c)) = true at h1
    change transversal c (label (D i c)) = false at h2
    have hr : label (D i c) = endpoint i true ∨ label (D i c) = endpoint i false := by
      simpa [rim] using h1
    rcases hr with h | h
    · have hh : c i ≠ true := by
        intro he
        rw [h, (trans_ep c i true).mpr he.symm] at h2
        cases h2
      simpa [Bool.eq_false_iff.mpr hh] using h
    · have hh : c i = true := by
        cases hc : c i
        · rw [h, (trans_ep c i false).mpr hc.symm] at h2
          cases h2
        · rfl
      simpa [hh] using h
  have wlab (i : Fin b) (p : Bool) (c : Fin b → Bool) :
      label (W i p c) = center b ∨ label (W i p c) = endpoint i p := by
    have h := (valid (spoke i p) (transversal c) (spoke_target i p) (trans_target c)).1
    change spoke i p (label (W i p c)) = true at h
    simpa [spoke] using h
  have whub (i : Fin b) (p : Bool) (c : Fin b → Bool) (h : c i = p) :
      label (W i p c) = center b := by
    have hv := (valid (spoke i p) (transversal c) (spoke_target i p) (trans_target c)).2
    change transversal c (label (W i p c)) = false at hv
    rcases wlab i p c with h0 | hp
    · exact h0
    · rw [hp, (trans_ep c i p).mpr h.symm] at hv
      cases hv
  have switch (i : Fin b) (p : Bool) (c : Fin b → Bool)
      (he : R i p = D i c) : W i p c = R i p :=
    cross _ _ _ _ (spoke_target i p) (hub_target b) (rim_target i) (trans_target c) he
  let group (i : Fin b) := Finset.univ.filter (fun l : Fin φ.leaves =>
    ∃ p, label l = endpoint i p)
  let hubGroup := Finset.univ.filter (fun l : Fin φ.leaves => label l = center b)
  let Bad (i : Fin b) := ∃ p : Bool, ∀ c : Fin b → Bool, c i ≠ p →
    label (W i p c) = endpoint i p
  let bads := Finset.univ.filter Bad
  have mem_group (i : Fin b) (l : Fin φ.leaves) (p : Bool)
      (h : label l = endpoint i p) : l ∈ group i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, h⟩
  have ep_ne (i : Fin b) : endpoint i true ≠ endpoint i false :=
    fun h => (by decide : true ≠ false) (endpoint_inj h).2
  have three (i : Fin b) : 3 ≤ (group i).card := by
    have hr : R i true ≠ R i false := distinct_label label (by rw [rlab, rlab]; exact ep_ne i)
    have d1 : label (D i (fun _ => false)) = endpoint i true := dlab _ _
    have d2 : label (D i (fun _ => true)) = endpoint i false := dlab _ _
    by_cases he : R i true = D i (fun _ => false)
    · have hn : R i false ≠ D i (fun _ => true) := by
        intro h
        have h₁ := cross _ _ _ _ (rim_target i) (trans_target (fun _ => false))
          (spoke_target i true) (hub_target b) he.symm
        have h₂ := cross _ _ _ _ (rim_target i) (trans_target (fun _ => true))
          (spoke_target i false) (hub_target b) h.symm
        exact distinct_label label (by rw [d1, d2]; exact ep_ne i) (h₁.symm.trans h₂)
      have hnr : R i true ≠ D i (fun _ => true) :=
        distinct_label label (by rw [rlab, d2]; exact ep_ne i)
      have hsub : {R i true, R i false, D i (fun _ => true)} ⊆ group i := by
        intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl | rfl
        · exact mem_group i _ true (rlab i true)
        · exact mem_group i _ false (rlab i false)
        · exact mem_group i _ false d2
      have hcard := Finset.card_le_card hsub
      simpa [Finset.card_insert_eq_ite, hr, hn, hnr] using hcard
    · have hn : R i false ≠ D i (fun _ => false) :=
        distinct_label label (by rw [rlab, d1]; exact (ep_ne i).symm)
      have hsub : {R i true, R i false, D i (fun _ => false)} ⊆ group i := by
        intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl | rfl
        · exact mem_group i _ true (rlab i true)
        · exact mem_group i _ false (rlab i false)
        · exact mem_group i _ true d1
      have hcard := Finset.card_le_card hsub
      simpa [Finset.card_insert_eq_ite, hr, hn, he] using hcard

  have four (i : Fin b) (hbad : ¬ Bad i) : 4 ≤ (group i).card := by
    have alt (p : Bool) : ∃ c : Fin b → Bool, c i ≠ p ∧
        label (W i p c) ≠ endpoint i p := by
      by_contra! hn
      exact hbad ⟨p, hn⟩
    obtain ⟨c, hc, hwc⟩ := alt true
    obtain ⟨d, hd, hwd⟩ := alt false
    have lc : label (D i c) = endpoint i true := by
      simpa [Bool.eq_false_iff.mpr hc] using dlab i c
    have ld : label (D i d) = endpoint i false := by
      have hd' : d i = true := by cases he : d i <;> simp_all
      simpa [hd'] using dlab i d
    have hnc : R i true ≠ D i c := fun he => hwc ((congrArg label (switch i true c he)).trans (rlab i true))
    have hnd : R i false ≠ D i d := fun he => hwd ((congrArg label (switch i false d he)).trans (rlab i false))
    let T : Finset (Fin φ.leaves) := {R i true, D i c}
    let F : Finset (Fin φ.leaves) := {R i false, D i d}
    have ht (l) (hl : l ∈ T) : label l = endpoint i true := by
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact rlab i true
      · exact lc
    have hfe (l) (hl : l ∈ F) : label l = endpoint i false := by
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact rlab i false
      · exact ld
    have hdis : Disjoint T F := Finset.disjoint_left.mpr (fun l ht' hf' => ep_ne i ((ht l ht').symm.trans (hfe l hf')))
    have hsub : T ∪ F ⊆ group i := by
      intro l hl
      rcases Finset.mem_union.mp hl with h | h
      · exact mem_group i l true (ht l h)
      · exact mem_group i l false (hfe l h)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis] at hcard
    simpa [T, F, Finset.card_insert_eq_ite, hnc, hnd] using hcard
  -- Every pair with fewer than four endpoint leaves forces its own center leaf.
  let pol (i : Fin b) : Bool := if h : Bad i then Classical.choose h else false
  have hpol (i : Fin b) (hi : Bad i) (c : Fin b → Bool) (hc : c i ≠ pol i) :
      label (W i (pol i) c) = endpoint i (pol i) := by
    simpa only [pol, dite_eq_left hi] using Classical.choose_spec hi c (by simpa only [pol, dite_eq_left hi] using hc)
  let base : Fin b → Bool := fun i => !(pol i)
  let diag (i j : Fin b) := if i = j then pol i else base j
  let hubSlot (i : Fin b) := W i (pol i) (diag i)
  have hhub (i : Fin b) : label (hubSlot i) = center b :=
    whub i (pol i) (diag i) (by simp [diag])
  have not_flip (i : Fin b) : base i ≠ pol i := by
    cases h : pol i <;> simp [base, h]
  have inj : Set.InjOn hubSlot (bads : Set (Fin b)) := by
    intro i hi j hj he
    by_contra hn
    have hcross : W i (pol i) (diag j) = hubSlot i :=
      cross _ _ _ _ (spoke_target i (pol i)) (trans_target (diag i))
        (spoke_target j (pol j)) (trans_target (diag j)) he
    have hne : diag j i ≠ pol i := by simpa [diag, Ne.symm hn] using not_flip i
    have hlabel := hpol i (Finset.mem_filter.mp hi).2 (diag j) hne
    rw [hcross, hhub] at hlabel
    exact endpoint_ne_center i (pol i) hlabel.symm
  let i0 : Fin b := ⟨0, by omega⟩
  let extra := W i0 (base i0) base
  have hextra : label extra = center b := whub i0 (base i0) base rfl
  have not_mem : extra ∉ bads.image hubSlot := by
    intro hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    have hcross : W i (pol i) base = hubSlot i :=
      cross _ _ _ _ (spoke_target i (pol i)) (trans_target (diag i))
        (spoke_target i0 (base i0)) (trans_target base) he
    have hlabel := hpol i (Finset.mem_filter.mp hi).2 base (not_flip i)
    rw [hcross, hhub] at hlabel
    exact endpoint_ne_center i (pol i) hlabel.symm
  have hub_count : bads.card + 1 ≤ hubGroup.card := by
    have hsub : insert extra (bads.image hubSlot) ⊆ hubGroup := by
      intro l hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hl with rfl | h
      · exact hextra
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
        exact hhub i
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem not_mem, Finset.card_image_of_injOn inj] at hh
  have pair_disj : ((Finset.univ : Finset (Fin b)) : Set (Fin b)).PairwiseDisjoint group := by
    intro i _ j _ hn
    apply Finset.disjoint_left.mpr
    intro l hi hj
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hj).2
    exact hn (endpoint_inj (hp.symm.trans hr)).1
  have hub_disj : Disjoint hubGroup (Finset.univ.biUnion group) := by
    apply Finset.disjoint_left.mpr
    intro l hh hg
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hi).2
    exact endpoint_ne_center i p (hp.symm.trans (Finset.mem_filter.mp hh).2)
  have total := Finset.card_le_card (Finset.subset_univ (hubGroup ∪ Finset.univ.biUnion group))
  rw [Finset.card_union_of_disjoint hub_disj, Finset.card_biUnion pair_disj,
    Finset.card_univ, Fintype.card_fin] at total
  have sums : (∑ _i : Fin b, 4) ≤ (∑ i : Fin b, (group i).card) + bads.card := by
    have hsum : (∑ i : Fin b, if Bad i then (1 : ℕ) else 0) = bads.card := by
      rw [← Finset.sum_filter]
      simp [bads]
    rw [← hsum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : Bad i
    · have h := three i
      simp [hi]
      omega
    · simpa [hi] using four i hi
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at sums
  omega

end PEqualNP.Outside.L_meta_218

open PEqualNP.Outside.L_meta_218 in

theorem PEqualNP.Outside.L_meta_218 : ∀ b s : ℕ, 1 ≤ b → ((∃ φ : PEqualNP.MetaComplexity.DMFormula (2 * b + 1), φ.leaves ≤ s ∧ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula (2 * b + 1) => Prop) (fun (_ : Fin (2 * b + 1)) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ ∧ ∀ x : Fin (2 * b + 1) → Bool, (φ.eval x = true ↔ ∃ u v : Fin (2 * b + 1), ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧ x u = true ∧ x v = true)) ↔ 4 * b + 1 ≤ s) := by
  intro b s hb
  constructor
  · rintro ⟨φ, hsize, hmono, heval⟩
    exact (leaf_bounds hb φ hmono heval).trans hsize
  · intro hs
    obtain ⟨φ, hsize, hmono, heval⟩ := construction b hb
    exact ⟨φ, hsize.le.trans hs, hmono, heval⟩
