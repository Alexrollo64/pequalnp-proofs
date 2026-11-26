import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_7700_318
    (single : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      ∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ t : Fin 14,
        gateVal 14 C j (fun i => decide (i = t)) = true → ∀ b : Fin 2, 14 ≤ opnd C j b)
    (ordered : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) → (gateAt C 0).op = GateOp.and →
      let row := fun (m : ℕ) (s : Fin 7) (i : Fin 14) => m.testBit (i.val / 7 * 7 + (i.val % 7 + s.val) % 7)
      let bit := fun (j t : ℕ) => gateVal 14 C j (fun i => decide (i.val = t))
      (∀ s, (∀ m ∈ ([129,130,136] : List ℕ), C.eval (List.ofFn (row m s)) = true) ∧
        ∀ m ∈ ([127,244,480,720,1188,3008,16256] : List ℕ), C.eval (List.ofFn (row m s)) = false) →
      (∀ j < C.size, (gateAt C j).op = GateOp.and → (bit j 0 = true ∨ bit j 7 = true) →
        ∀ b : Fin 2, 14 ≤ opnd C j b) →
      ∀ i j : Fin C.size, i < j → (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
        bit i 7 = true → bit i 0 = false → bit j 0 = true → bit j 7 = false → False) :
(∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∃ x7 < x1.size,                 ∃ x8 < x1.size,                   (0 : ℕ) < x7 ∧                     (0 : ℕ) < x8 ∧                       x7 ≠ x8 ∧                         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                           (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                             have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = (0 : Fin (14 : ℕ))));                             have x10 : List Bool := x1.wires (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = (7 : Fin (14 : ℕ))));                             x10.getD ((14 : ℕ) + x7) Bool.false = Bool.true ∧ x9.getD ((14 : ℕ) + x7) Bool.false = Bool.false ∧ x9.getD ((14 : ℕ) + x8) Bool.false = Bool.true ∧ x10.getD ((14 : ℕ) + x8) Bool.false = Bool.false) →               False) := by
  have gateDef (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) : gateVal n C j x = (C.wires (List.ofFn x)).getD (n+j) false := rfl
  have atDef (C : Circuit) (j : ℕ) : gateAt C j = C.gates.getD j ⟨.or,[]⟩ := rfl
  have sizeDef (C : Circuit) : C.size = C.gates.length := rfl
  have portDef (C : Circuit) (j : ℕ) (b : Fin 2) : opnd C j b = (gateAt C j).inputs.getD b 0 := rfl
  intro C budget legal distinct first computes marked
  let E := fun x : Fin 14 → Bool => ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
  change ∀ x, C.eval (List.ofFn x) = true ↔ E x at computes
  let bit := fun (D : Circuit) (j t : ℕ) => gateVal 14 D j (fun i => decide (i.val = t))
  have congr0 : (fun i : Fin 14 => decide (i.val = 0)) = (fun i => decide (i = 0)) := by decide +kernel
  have congr7 : (fun i : Fin 14 => decide (i.val = 7)) = (fun i => decide (i = 7)) := by decide +kernel
  have finish (D : Circuit) (bd : D.size ≤ 27) (ao : IsAO2 14 D)
      (ds : ∀ j < D.size, opnd D j 0 ≠ opnd D j 1) (fst : (gateAt D 0).op = GateOp.and)
      (spec : ∀ x, D.eval (List.ofFn x) = true ↔ E x)
      (i j : Fin D.size) (ij : i < j) (ai : (gateAt D i).op = GateOp.and) (aj : (gateAt D j).op = GateOp.and)
      (i7 : bit D i 7 = true) (i0 : bit D i 0 = false) (j0 : bit D j 0 = true) (j7 : bit D j 7 = false) : False := by
    let row := fun (m : ℕ) (s : Fin 7) (v : Fin 14) => m.testBit (v.val / 7 * 7 + (v.val % 7 + s.val) % 7)
    have rows : ∀ s, (∀ m ∈ ([129,130,136] : List ℕ), E (row m s)) ∧
        ∀ m ∈ ([127,244,480,720,1188,3008,16256] : List ℕ), ¬ E (row m s) := by
      unfold E row; decide +kernel
    have inc : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l+1 ∨ p = l+3 := by decide +kernel
    have canon := single D bd ao (by intro x; simpa only [inc,E] using spec x)
    apply ordered D bd ao ds fst _ _ i j ij ai aj i7 i0 j0 j7
    · intro s
      constructor
      · intro m hm; exact (spec _).2 ((rows s).1 m hm)
      · intro m hm; apply Bool.eq_false_iff.mpr
        exact fun h => (rows s).2 m hm ((spec _).1 h)
    · intro k hk hA isOn
      rcases isOn with h | h
      · apply canon k hk hA 0; simpa only [←congr0] using h
      · apply canon k hk hA 7; simpa only [←congr7] using h
  obtain ⟨i,hi,j,hj,_,_,ne,ai,aj,i7,i0,j0,j7⟩ := marked
  change (C.wires _).getD _ _ = true at i7 j0
  change (C.wires _).getD _ _ = false at i0 j7
  have m1 : bit C i 7 = true := by simpa only [bit,gateDef,congr7] using i7
  have m2 : bit C i 0 = false := by simpa only [bit,gateDef,congr0] using i0
  have m3 : bit C j 0 = true := by simpa only [bit,gateDef,congr0] using j0
  have m4 : bit C j 7 = false := by simpa only [bit,gateDef,congr7] using j7
  rcases lt_or_gt_of_ne ne with ij | ji
  · exact finish C budget legal distinct first computes ⟨i,hi⟩ ⟨j,hj⟩ ij ai aj m1 m2 m3 m4
  let τ : Fin 14 → Fin 14 := ![7,13,12,11,10,9,8,0,6,5,4,3,2,1]
  have invol : ∀ a, τ (τ a) = a := by decide +kernel
  let w := fun k : ℕ => if h : k < 14 then (τ ⟨k,h⟩).val else k
  have ww (k : ℕ) : w (w k) = k := by
    by_cases h : k < 14
    · simp [w,h,(τ ⟨k,h⟩).isLt,invol]
    · simp [w,h]
  let rename := fun g : Gate => (⟨g.op,g.inputs.map w⟩ : Gate)
  let D : Circuit := ⟨C.gates.map rename,w C.output⟩
  have sz : D.size = C.size := by simp [D,sizeDef]
  have read (k : ℕ) (hk : k < C.size) : gateAt D k = rename (gateAt C k) := by
    have h : k < C.gates.length := hk
    simp [D,atDef,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h]
  have port (k : ℕ) (hk : k < C.size) (b : Fin 2) : opnd D k b = w (opnd C k b) := by
    have h : k < C.gates.length := hk
    have mem : gateAt C k ∈ C.gates := by simp [atDef,List.getD_eq_getElem?_getD,h]
    have len := legal.2.2 _ mem
    have hb : b.val < (gateAt C k).inputs.length := by rw [len]; exact b.isLt
    simp [portDef,read k hk,rename,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,hb]
  have lew (k v : ℕ) (h : v < 14+k) : w v < 14+k := by
    unfold w; split <;> rename_i h'
    · have := (τ ⟨v,h'⟩).isLt; omega
    · exact h
  have aoD : IsAO2 14 D := by
    refine ⟨?_,?_,?_⟩
    · intro g hg; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg; exact legal.1 a ha
    · intro k hk v hv
      have hk' : k < C.size := by simpa [D,sizeDef] using hk
      rw [read k hk'] at hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
      exact lew k a (legal.2.1 k hk' a ha)
    · intro g hg; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg; simpa [rename] using legal.2.2 a ha
  have dsD (k : ℕ) (hk : k < D.size) : opnd D k 0 ≠ opnd D k 1 := by
    rw [sz] at hk; rw [port k hk,port k hk]
    intro h; exact distinct k hk (by simpa only [ww] using congrArg w h)
  let run := fun (gs : List Gate) (a : List Bool) =>
    gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]) a
  have snoc (a : List Bool) (v : Bool) (k : ℕ) : (a ++ [v]).getD k false =
      (if k < a.length then a.getD k false else if k = a.length then v else false) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append]
    split_ifs with h e
    · rfl
    · subst e; simp
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl
  have coupled (gs : List Gate) (a b : List Bool) (len : a.length = b.length) (lb : 14 ≤ a.length)
      (eqv : ∀ k, b.getD (w k) false = a.getD k false) (k : ℕ) :
      (run (gs.map rename) b).getD (w k) false = (run gs a).getD k false := by
    induction gs generalizing a b with
    | nil => exact eqv k
    | cons g tail ih =>
      let val := g.op.eval (g.inputs.map (fun k => a.getD k false))
      have same : (rename g).op.eval ((rename g).inputs.map (fun k => b.getD k false)) = val := by
        simp only [rename,List.map_map,Function.comp_def,eqv,val]
      change (run (tail.map rename) (b ++ [_])).getD _ _ = (run tail (a ++ [val])).getD _ _
      rw [same]
      apply ih _ _ (by simp [len]) (by simp; omega)
      intro r
      rw [snoc,snoc,←len,eqv]
      by_cases hr : r < 14
      · have wr : w r < 14 := by simpa [w,hr] using (τ ⟨r,hr⟩).isLt
        simp [show r < a.length by omega,show w r < a.length by omega]
      · simp [w,hr]
  have transport (x : Fin 14 → Bool) (k : ℕ) :
      (D.wires (List.ofFn x)).getD (w k) false =
      (C.wires (List.ofFn fun a => x (τ a))).getD k false := by
    apply coupled C.gates _ _ (by simp) (by simp)
    intro i; by_cases h : i < 14
    · simp only [w,h,dite_true,List.getD_eq_getElem?_getD,List.getElem?_ofFn,(τ ⟨i,h⟩).isLt,Option.getD_some]
    · simp only [w,h,dite_false,List.getD_eq_getElem?_getD,List.getElem?_ofFn,Option.getD_none]
  let neg := fun v : Fin 7 => -v
  have pt : ∀ p : Fin 7, τ (Fin.castAdd 7 p) = Fin.natAdd 7 (neg p) := by decide +kernel
  have ln : ∀ l : Fin 7, τ (Fin.natAdd 7 l) = Fin.castAdd 7 (neg l) := by decide +kernel
  have incSwap : ∀ p l : Fin 7, (p = l ∨ p=l+1 ∨ p=l+3) →
      (neg l = neg p ∨ neg l = neg p+1 ∨ neg l = neg p+3) := by decide +kernel
  have flip (x : Fin 14 → Bool) : E (fun a => x (τ a)) → E x := by
    rintro ⟨p,l,e,a,b⟩
    exact ⟨neg l,neg p,incSwap p l e,ln l ▸ b,pt p ▸ a⟩
  have specD (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔ E x := by
    change (D.wires _).getD (w C.output) false = true ↔ _
    rw [transport]
    change C.eval (List.ofFn fun a => x (τ a)) = true ↔ E x
    rw [computes]
    exact ⟨flip x,fun h => flip (fun a => x (τ a)) (by simpa only [invol] using h)⟩
  have s07 : (fun a : Fin 14 => decide ((τ a).val = 0)) = (fun a => decide (a.val = 7)) := by decide +kernel
  have s70 : (fun a : Fin 14 => decide ((τ a).val = 7)) = (fun a => decide (a.val = 0)) := by decide +kernel
  have v0 (k : ℕ) : bit D k 0 = bit C k 7 := by
    have h := transport (fun a => decide (a.val = 0)) (14+k)
    simpa only [bit,gateDef,w,show ¬ 14+k < 14 by omega,dite_false,s07] using h
  have v7 (k : ℕ) : bit D k 7 = bit C k 0 := by
    have h := transport (fun a => decide (a.val = 7)) (14+k)
    simpa only [bit,gateDef,w,show ¬ 14+k < 14 by omega,dite_false,s70] using h
  have pos : 0 < C.size := by omega
  exact finish D (sz ▸ budget) aoD dsD (by rw [read 0 pos]; exact first) specD
    ⟨j,sz ▸ hj⟩ ⟨i,sz ▸ hi⟩ ji (by rw [read j hj];exact aj) (by rw [read i hi];exact ai)
    (by rw [v7]; exact m3) (by rw [v0]; exact m4) (by rw [v0]; exact m1) (by rw [v7]; exact m2)
