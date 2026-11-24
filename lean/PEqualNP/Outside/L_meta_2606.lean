import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2606_aux

private def addGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem eval_imp (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    {u v : List Bool} (h : ∀ i, u.getD i false = true → v.getD i false = true) :
    g.op.eval (g.inputs.map fun i => u.getD i false) = true →
      g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
  rcases hg with ho | ho
  · simp only [ho, GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro hu _ ⟨i, hi, rfl⟩
    exact h i (hu _ ⟨i, hi, rfl⟩)
  · simp only [ho, GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨_, ⟨i, hi, rfl⟩, hu⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hu⟩

private theorem fold_imp (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (u v : List Bool) (hlen : u.length = v.length)
    (huv : ∀ i, u.getD i false = true → v.getD i false = true) :
    ∀ i, (gs.foldl addGate u).getD i false = true →
      (gs.foldl addGate v).getD i false = true := by
  induction gs generalizing u v with
  | nil => exact huv
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
    · simp [addGate, hlen]
    · intro i hi
      unfold addGate at hi ⊢
      by_cases h : i < u.length
      · rw [List.getD_append _ _ _ _ h] at hi
        rw [List.getD_append _ _ _ _ (hlen ▸ h)]
        exact huv i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
        cases he : i - u.length with
        | zero =>
          rw [he] at hi
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_imp g (hgs g List.mem_cons_self) huv hi
        | succ k => rw [he] at hi; simp at hi

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl addGate w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, addGate]; omega

private theorem fold_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl addGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [addGate]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem and_wire (C : Circuit) (n j a b : ℕ) (x : Fin n → Bool)
    (hback : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hg : C.gates[j]? = some ⟨.and, [a,b]⟩) :
    PEqualNP.BlindGate.wireValue C n x (n+j) =
      (PEqualNP.BlindGate.wireValue C n x a && PEqualNP.BlindGate.wireValue C n x b) := by
  obtain ⟨hj, hgate⟩ := List.getElem?_eq_some_iff.mp hg
  have hab (i : ℕ) (hi : i ∈ [a,b]) : i < n + j := by
    apply hback j hj
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
    exact hi
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by simp
  let pre := (C.gates.take j).foldl addGate (List.ofFn x)
  have hlen : pre.length = n+j := by
    rw [show pre = (C.gates.take j).foldl addGate (List.ofFn x) from rfl, fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  let next := addGate pre C.gates[j]
  have hnext : next.length = n+j+1 := by simp [next, addGate, hlen]
  have hw : C.wires (List.ofFn x) = (C.gates.drop (j+1)).foldl addGate next := by
    change C.gates.foldl addGate (List.ofFn x) = _
    conv_lhs => rw [hsplit]
    simp only [List.foldl_append, List.foldl_cons]
    rfl
  have hprev (i : ℕ) (hi : i < n+j) : (C.wires (List.ofFn x)).getD i false = pre.getD i false := by
    rw [hw, fold_read _ _ _ (by omega)]
    exact List.getD_append _ _ _ _ (by omega)
  unfold PEqualNP.BlindGate.wireValue
  rw [hprev a (hab a (by simp)), hprev b (hab b (by simp)), hw, fold_read _ _ _ (by omega)]
  change (addGate pre C.gates[j]).getD (n+j) false = _
  rw [hgate]
  simp only [addGate]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen, GateOp.eval]

end PEqualNP.Outside.L_meta_2606_aux

open PEqualNP.Outside.L_meta_2606_aux in
theorem PEqualNP.Outside.L_meta_2606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 x2 x1 → (∀ (x4 : ℕ), Monotone fun (x5 : Fin x2 → Bool) => PEqualNP.BlindGate.wireValue x1 x2 x5 x4) ∧ ∀ (x4 x5 x6 : ℕ), x1.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → ∀ (x8 : Fin x2 → Bool), PEqualNP.BlindGate.wireValue x1 x2 x8 (x2 + x4) = (PEqualNP.BlindGate.wireValue x1 x2 x8 x5 && PEqualNP.BlindGate.wireValue x1 x2 x8 x6) := by
  intro C n hC
  constructor
  · intro w x y hxy
    have hin (i : ℕ) (hx : (List.ofFn x).getD i false = true) :
        (List.ofFn y).getD i false = true := by
      by_cases hi : i < n
      · have hxt : x ⟨i,hi⟩ = true := by
          simpa [List.getD_eq_getElem?_getD, hi] using hx
        have hyt : y ⟨i,hi⟩ = true := by
          have hle : true ≤ y ⟨i,hi⟩ := hxt ▸ hxy ⟨i,hi⟩
          cases hy : y ⟨i,hi⟩ with
          | false =>
            rw [hy] at hle
            exact False.elim ((by decide : ¬ true ≤ false) hle)
          | true => rfl
        simpa [List.getD_eq_getElem?_getD, hi] using hyt
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)] at hx
        contradiction
    have hw := fold_imp C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp) hin w
    change (C.gates.foldl addGate (List.ofFn x)).getD w false ≤
      (C.gates.foldl addGate (List.ofFn y)).getD w false
    cases ha : (C.gates.foldl addGate (List.ofFn x)).getD w false
    · simp
    · rw [hw ha]
  · intro j a b hg x
    exact and_wire C n j a b x hC.2.1 hg
