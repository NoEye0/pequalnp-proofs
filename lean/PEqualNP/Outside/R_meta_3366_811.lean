import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3366_811
    (normalize : ∀ C : Circuit, FanInTwo C →
      ∃ D : Circuit, D.size = C.size ∧
        (∀ j g, D.gates[j]? = some g →
          (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
            (g.op = .not ∧ g.inputs.length = 1)) ∧ ∀ i ∈ g.inputs, i < 11 + j) ∧
        ∀ w : List Bool, w.length = 11 → w.getD 0 false = false → D.eval w = C.eval w)
    (noTable : ∀ D : Circuit, D.size ≤ 13 →
      (∀ j g, D.gates[j]? = some g →
        (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
          (g.op = .not ∧ g.inputs.length = 1)) ∧ ∀ i ∈ g.inputs, i < 11 + j) →
      (∀ r : Fin 512,
        let x : Fin 9 → Bool := fun i => r.val.testBit i.val
        D.eval (List.ofFn (fun i : Fin 9 => if i = 0 then false else x i) ++
          [x 0 || x 4, x 0 || x 3]) =
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
          (fun e => x e.1 && x e.2)) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False := by
  intro f C hc hs he
  obtain ⟨D, hsize, hnormal, hvalue⟩ := normalize C hc
  apply noTable D (hsize.trans_le hs) hnormal
  intro r
  let x : Fin 9 → Bool := fun i => r.val.testBit i.val
  have hx : (fun i : Fin 9 => if i = 0 then false else x i) = Function.update x 0 false := by
    funext i
    by_cases h : i = 0 <;> simp [h, Function.update_of_ne]
  let w := List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]
  have hlen : w.length = 11 := by simp [w]
  have hzero : w.getD 0 false = false := by
    unfold w
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp
  dsimp only
  change D.eval (List.ofFn (fun i : Fin 9 => if i = 0 then false else x i) ++
    [x 0 || x 4, x 0 || x 3]) = _
  rw [hx]
  exact (hvalue w hlen hzero).trans (he x)
