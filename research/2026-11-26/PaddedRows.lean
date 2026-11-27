import Mask31917056Lower
import PEqualNP.Outside.L_meta_20709

namespace Alexrollo64.PaddedRows

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Replace input references. Generated wire numbers move with the input length. -/
def rename (old new : Nat) (input : Nat → Nat) (i : Nat) :=
  if i < old then input i else new + (i-old)

def mapGate (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def mapCircuit (f : Nat → Nat) (c : Circuit) : Circuit :=
  ⟨c.gates.map (mapGate f), f c.output⟩

theorem mono_map {c : Circuit} (f : Nat → Nat) (h : Monotone2 c) :
    Monotone2 (mapCircuit f c) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa [mapGate] using h a ha

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem replay (x y : List Bool) (gs : List Gate) (input : Nat → Nat) (used : List Bool)
    (raw : ∀ zs : List Bool, zs.length ≤ used.length + gs.length → ∀ i < x.length,
      (y ++ zs).getD (input i) false = x.getD i false) :
    ∃ zs : List Bool, zs.length = used.length + gs.length ∧
      gs.foldl step (x ++ used) = x ++ zs ∧
      (gs.map (mapGate (rename x.length y.length input))).foldl step (y ++ used) = y ++ zs := by
  induction gs generalizing used with
  | nil => exact ⟨used,by simp,rfl,rfl⟩
  | cons g gs ih =>
    let f := rename x.length y.length input
    have reads (i : Nat) : (y ++ used).getD (f i) false = (x ++ used).getD i false := by
      by_cases h : i < x.length
      · simpa only [f,rename,if_pos h,List.getD_append _ _ _ _ h] using raw used (by simp) i h
      · have h' : x.length ≤ i := by omega
        unfold f rename
        rw [if_neg h,List.getD_append_right _ _ _ _ h',List.getD_append_right _ _ _ _ (by omega)]
        simp
    let v := g.op.eval (g.inputs.map fun i => (x ++ used).getD i false)
    let next := used ++ [v]
    have hn : next.length = used.length+1 := by simp [next]
    have eqy : step (y ++ used) (mapGate f g) = y ++ next := by
      simp only [step,mapGate,List.map_map,Function.comp_def,reads,v,next,List.append_assoc]
    obtain ⟨zs,hz,hx,hy⟩ := ih next (by intro l hl; apply raw l; simp only [List.length_cons]; omega)
    exact ⟨zs,by simp only [List.length_cons]; omega,by simpa [step,next,v,List.append_assoc] using hx,
      by change (gs.map (mapGate f)).foldl step (step (y ++ used) (mapGate f g)) = y ++ zs
         rw [eqy]; exact hy⟩

theorem map_eval (x y : List Bool) (c : Circuit) (input : Nat → Nat)
    (raw : ∀ zs : List Bool, zs.length ≤ c.size → ∀ i < x.length,
      (y ++ zs).getD (input i) false = x.getD i false) :
    (mapCircuit (rename x.length y.length input) c).eval y = c.eval x := by
  obtain ⟨zs,hz,hx,hy⟩ := replay x y c.gates input [] (by simpa [Circuit.size] using raw)
  simp only [List.append_nil,List.length_nil,Nat.zero_add] at hx hy hz
  unfold Circuit.eval
  change ((c.gates.map _).foldl step y).getD _ false = (c.gates.foldl step x).getD _ false
  rw [hy,hx]
  by_cases h : c.output < x.length
  · simpa only [mapCircuit,rename,if_pos h,List.getD_append _ _ _ _ h] using raw zs (by simpa [Circuit.size,hz]) c.output h
  · have h' : x.length ≤ c.output := by omega
    simp only [mapCircuit,rename,if_neg h,List.getD_append_right _ _ _ _ h',
      List.getD_append_right y zs false _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem one_read {n m : Nat} (u : Fin n) (v : Fin m) (i : Nat) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = n+v.val)) := by
  unfold oneEach
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by simpa)]
    have h : i ≠ n+v.val := by omega
    simp [List.getD_eq_getElem?_getD,hi,h,Fin.ext_iff]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    have h : i ≠ u.val := by omega
    by_cases hj : i-n < m
    · have he : i-n = v.val ↔ i = n+v.val := by omega
      simp [List.getD_eq_getElem?_getD,h,hi,hj,Fin.ext_iff,he]
    · have he : i ≠ n+v.val := by omega
      simp [List.getD_eq_getElem?_getD,h,hj,he]

def target (k : Nat) (u : Fin (5+k)) (v : Fin 5) :=
  if u.val < 5 then (31917056 : Nat).testBit (5*u.val+v.val) else false

/-- Relabel a vertex, or use a missing wire if it lies outside the selected vertices. -/
noncomputable def back {n N : Nat} (e : Fin n ↪ Fin N) (i base cap : Nat) : Nat := by
  classical
  exact if h : ∃ a, (e a).val = i then base + h.choose.val else cap

/-- Restricting any represented bipartite graph to subsets of its vertices preserves
the upper gate budget. The chosen row and column orderings may be arbitrary. -/
theorem induced {n m N M budget : Nat} {A : Fin N → Fin M → Bool}
    (rows : Fin n ↪ Fin N) (cols : Fin m ↪ Fin M) (hc : RepSizeAtMost A budget) :
    RepSizeAtMost (fun u v => A (rows u) (cols v)) budget := by
  classical
  obtain ⟨c,hm,hs,hr⟩ := hc
  let cap := n+m+c.size
  let pin := fun i => if i < N then back rows i 0 cap else back cols (i-N) n cap
  let f := rename (N+M) (n+m) pin
  refine ⟨mapCircuit f c,mono_map f hm,by simpa [mapCircuit,Circuit.size] using hs,?_⟩
  intro u v
  let x := oneEach (rows u) (cols v)
  let y := oneEach u v
  have hx : x.length = N+M := by simp [x,oneEach]
  have hy : y.length = n+m := by simp [y,oneEach]
  have eq := map_eval x y c pin (by
    intro zs hz i hi
    have missing : (y ++ zs).getD cap false = false :=
      List.getD_eq_default _ _ (by simp [hy,cap]; omega)
    by_cases left : i < N
    · simp only [pin,if_pos left,back]
      split_ifs with h
      · let a := h.choose
        have he : (rows a).val = i := h.choose_spec
        have iff' : a.val = u.val ↔ i = (rows u).val := by
          rw [← he,Fin.val_inj,Fin.val_inj,EmbeddingLike.apply_eq_iff_eq]
        simp only [Nat.zero_add]
        rw [List.getD_append _ _ _ _ (by change a.val < y.length; rw [hy]; omega)]
        change (oneEach u v).getD a.val false = (oneEach (rows u) (cols v)).getD i false
        rw [one_read,one_read]
        simp [iff',show a.val ≠ n+v.val by omega,show i ≠ N+(cols v).val by omega]
      · rw [missing]; change false = (oneEach (rows u) (cols v)).getD i false
        rw [one_read]
        have h1 : i ≠ (rows u).val := fun he => h ⟨u,he.symm⟩
        simp [h1,show i ≠ N+(cols v).val by omega]
    · simp only [pin,if_neg left,back]
      split_ifs with h
      · let b := h.choose
        have he : (cols b).val = i-N := h.choose_spec
        have iff' : b.val = v.val ↔ i = N+(cols v).val := by
          have e : b.val = v.val ↔ (cols b).val = (cols v).val := by
            rw [Fin.val_inj,Fin.val_inj,EmbeddingLike.apply_eq_iff_eq]
          rw [e,he]; omega
        rw [List.getD_append _ _ _ _ (by change n+b.val < y.length; rw [hy]; omega)]
        change (oneEach u v).getD (n+b.val) false = (oneEach (rows u) (cols v)).getD i false
        rw [one_read,one_read]
        simp [show n+b.val ≠ u.val by omega,show i ≠ (rows u).val by omega,iff']
      · rw [missing]; change false = (oneEach (rows u) (cols v)).getD i false
        rw [one_read]
        have h2 : i ≠ N+(cols v).val := by intro he; exact h ⟨v,by omega⟩
        simp [h2,show i ≠ (rows u).val by omega])
  rw [hx,hy] at eq
  exact eq.trans (hr _ _)

/-- The original hard table as an induced submatrix forces at least eight gates. -/
theorem contains_mask_lower {N M : Nat} {A : Fin N → Fin M → Bool}
    (rows : Fin 5 ↪ Fin N) (cols : Fin 5 ↪ Fin M)
    (hA : ∀ u v, A (rows u) (cols v) = (31917056 : Nat).testBit (5*u.val+v.val)) :
    ¬ RepSizeAtMost A 7 := by
  intro hc
  apply Alexrollo64.Support20782.mask31917056_lower
  have h := induced rows cols hc
  simpa only [hA] using h

theorem lower (k : Nat) : ¬ RepSizeAtMost (target k) 7 := by
  let rows : Fin 5 ↪ Fin (5+k) := ⟨fun u => ⟨u.val, by omega⟩,
    fun a b he => Fin.ext (congrArg (fun z : Fin (5+k) => z.val) he)⟩
  apply contains_mask_lower rows (Function.Embedding.refl _)
  intro u v
  change (if u.val < 5 then _ else false) = _
  rw [if_pos u.isLt]
  rfl

/-- A sixth row code represents any added empty row. -/
def pattern (r : Fin 6) (v : Fin 5) := List.ofFn fun i : Fin 10 =>
  decide (i.val < 5 ∧ i.val = r.val) || decide (i.val = 5 + v.val)

theorem base_values : ∀ r : Fin 6, ∀ v : Fin 5,
    PEqualNP.Outside.L_meta_20709.witness.eval (pattern r v) =
      (if r.val < 5 then (31917056 : Nat).testBit (5*r.val+v.val) else false) := by
  decide +kernel

theorem upper (k : Nat) : RepSizeAtMost (target k) 8 := by
  let c := PEqualNP.Outside.L_meta_20709.witness
  let pin := fun i => if i < 5 then i else i+k
  let f := rename 10 (5+k+5) pin
  refine ⟨mapCircuit f c,mono_map f PEqualNP.Outside.L_meta_20709.witnessFit,by simp [Circuit.size,mapCircuit,c,PEqualNP.Outside.L_meta_20709.witness],?_⟩
  intro u v
  let r : Fin 6 := ⟨min u.val 5,by omega⟩
  let x := pattern r v
  let y := oneEach u v
  have hx : x.length = 10 := by simp [x,pattern]
  have hy : y.length = 5+k+5 := by simp [y,oneEach]
  have eq := map_eval x y c pin (by
    intro zs hz i hi
    rw [hx] at hi
    have hp : pin i < y.length := by dsimp [pin]; rw [hy]; split <;> omega
    rw [List.getD_append _ _ _ _ hp]
    change (oneEach u v).getD (pin i) false = (pattern r v).getD i false
    rw [one_read]
    simp only [pattern,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dif_pos,Option.getD_some]
    by_cases h : i < 5
    · have e : i = u.val ↔ i = r.val := by dsimp [r]; omega
      simp [pin,h,e,show i ≠ 5+k+v.val by omega,show i ≠ 5+v.val by omega]
    · have e : i+k = 5+k+v.val ↔ i = 5+v.val := by omega
      simp [pin,h,e,show i+k ≠ u.val by omega])
  rw [hx,hy] at eq
  refine eq.trans ((base_values r v).trans ?_)
  by_cases h : u.val < 5
  · simp [target,r,h,Nat.min_eq_left h.le]
  · simp [target,r,h,Nat.min_eq_right (by omega : 5 ≤ u.val)]

theorem exact_eight (k : Nat) : RepSizeAtMost (target k) 8 ∧ ¬ RepSizeAtMost (target k) 7 :=
  ⟨upper k,lower k⟩

#print axioms induced
#print axioms contains_mask_lower
#print axioms exact_eight
end Alexrollo64.PaddedRows
