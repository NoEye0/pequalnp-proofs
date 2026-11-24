import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Circuit monotonicity follows the fold argument of L-meta-1373.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3014_811
    (cover : ∀ s : Fin 128, ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ).any (fun r => decide (
      (∀ p : Fin 7, s.val.testBit p.val = true → r.testBit p.val = true) ∧
      (∀ j : Fin 7, (∀ p : Fin 7, (p.val, j.val + 7) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) →
        s.val.testBit p.val = false) → r.testBit (j.val + 7) = true))) = true)
    (witness : ∃ C : Circuit, IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      2 ≤ C.size ∧ C.size ≤ 26 ∧
      (∀ r ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), C.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val)) = true) ∧
      (∀ r ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), C.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val)) = false)) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (2 : ℕ) ≤ x3.size ∧ x3.size ≤ (26 : ℕ) ∧ (∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.true → (∀ x6 ≤ x4, x2 x6 = Bool.true → x6 = x4) → x3.eval (List.ofFn x4) = Bool.true) ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.false → (∀ (x6 : Fin (14 : ℕ) → Bool), x4 ≤ x6 → x2 x6 = Bool.false → x6 = x4) → x3.eval (List.ofFn x4) = Bool.false := by
  obtain ⟨C, hmodel, hdistinct, hlo, hhi, accept, reject⟩ := witness
  let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let row (r : ℕ) (i : Fin 14) := r.testBit i.val
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have compare (L : List Gate) (a b : List Bool)
      (hops : ∀ g ∈ L, g.op = GateOp.and ∨ g.op = GateOp.or)
      (hlen : a.length = b.length) (h : ∀ i, a.getD i false = true → b.getD i false = true) :
      ∀ i, (L.foldl step a).getD i false = true → (L.foldl step b).getD i false = true := by
    induction L generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      apply ih (step a g) (step b g) (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
      · simp [step, hlen]
      · intro i
        have hv : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
            g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
          rcases hops g List.mem_cons_self with e | e
          · rw [e]
            simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
            exact fun ha j hj => h j (ha j hj)
          · rw [e]
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
            rintro ⟨j, hj, ha⟩
            exact ⟨j, hj, h j ha⟩
        unfold step
        rcases lt_trichotomy i a.length with hlt | he | hgt
        · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
          exact h i
        · subst i
          rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),
            List.getD_append_right _ _ _ _ (by omega), Nat.sub_self, ← hlen, Nat.sub_self]
          exact hv
        · rw [List.getD_eq_default _ _ (by simp; omega)]
          simp
  have mono (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    apply compare C.gates (List.ofFn x) (List.ofFn y) hmodel.1 (by simp)
    intro i hi
    by_cases hb : i < 14
    · rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_ofFn] at hi ⊢
      exact h ⟨i, hb⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      contradiction
  have edgeMask : ∀ p l : Fin 14, (p.val, l.val) ∈ E →
      2 ^ p.val + 2 ^ l.val ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ) ∧
      ∀ j : Fin 14, row (2 ^ p.val + 2 ^ l.val) j = true → j = p ∨ j = l := by
    decide +kernel
  refine ⟨C, hmodel, hdistinct, hlo, hhi, ?_, ?_⟩
  · intro x hx _
    change decide (∃ p l : Fin 14, (p.val, l.val) ∈ E ∧ x p = true ∧ x l = true) = true at hx
    obtain ⟨p, l, hp, hxp, hxl⟩ := of_decide_eq_true hx
    obtain ⟨hm, hs⟩ := edgeMask p l hp
    exact mono (row (2 ^ p.val + 2 ^ l.val)) x
      (fun j hj => (hs j hj).elim (fun e => e ▸ hxp) (fun e => e ▸ hxl)) (accept _ hm)
  · intro x hx _
    change decide (∃ p l : Fin 14, (p.val, l.val) ∈ E ∧ x p = true ∧ x l = true) = false at hx
    let bits := BitVec.ofBoolListLE (List.ofFn (fun p : Fin 7 => x (Fin.castAdd 7 p)))
    let s : Fin 128 := ⟨bits.toNat, by simpa [bits] using bits.isLt⟩
    have hs (p : Fin 7) : s.val.testBit p.val = x (Fin.castAdd 7 p) := by
      change bits.getLsbD p.val = _
      rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa using p.isLt), List.getElem_ofFn]
    obtain ⟨r, hr, hrow⟩ := List.any_eq_true.mp (cover s)
    obtain ⟨hleft, hright⟩ := of_decide_eq_true hrow
    have dominates (i : Fin 14) : x i = true → row r i = true := by
      refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
      · intro p hp
        exact hleft p ((hs p).trans hp)
      · intro j hj
        change r.testBit (7 + j.val) = true
        rw [Nat.add_comm 7]
        apply hright j
        intro p hp
        rw [hs]
        cases e : x (Fin.castAdd 7 p)
        · rfl
        · have hit : ∃ p l : Fin 14, (p.val, l.val) ∈ E ∧ x p = true ∧ x l = true :=
            ⟨Fin.castAdd 7 p, Fin.natAdd 7 j, by simpa [E, Nat.add_comm] using hp, e, hj⟩
          have z : false = true := hx.symm.trans (decide_eq_true hit)
          exact Bool.noConfusion z
    by_contra! t
    have htrue : C.eval (List.ofFn x) = true := by simpa using t
    have contr := mono x (row r) dominates htrue
    rw [reject _ hr] at contr
    contradiction
