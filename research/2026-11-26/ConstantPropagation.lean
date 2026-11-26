import PEqualNP.Defs.CircuitLowerBounds

namespace Alexrollo64.ConstantPropagation
open PEqualNP.CircuitLowerBounds

inductive Arg where
  | lit : Bool → Arg
  | wire : Nat → Arg

def Arg.val (w : List Bool) : Arg → Bool
  | .lit v => v
  | .wire i => w.getD i false

inductive Step where
  | alias : Arg → Step
  | binary : Bool → Nat → Nat → Step -- true for AND, false for OR
  | neg : Nat → Step

def Step.gates : Step → List Gate
  | .alias _ => []
  | .binary andOp a b => [⟨if andOp then .and else .or, [min a b,max a b]⟩]
  | .neg a => [⟨.not,[a]⟩]

def Step.result (cap : Nat) : Step → Arg
  | .alias a => a
  | _ => .wire cap

def applyOp (op a b : Bool) : Bool := if op then a && b else a || b

def combine (op : Bool) : Arg → Arg → Step
  | .lit v, a | a, .lit v => .alias (if v == op then a else .lit v)
  | .wire i, .wire j => .binary op i j

def negate : Arg → Step
  | .lit v => .alias (.lit (!v))
  | .wire i => .neg i

def simplify (op : GateOp) (args : List Arg) : Step :=
  match op, args with
  | .and, [] => .alias (.lit true)
  | .or, [] => .alias (.lit false)
  | .and, [a] | .or, [a] => .alias a
  | .and, a::b::_ => combine true a b
  | .or, a::b::_ => combine false a b
  | .not, a::_ => negate a
  | .not, [] => .alias (.lit true)
  | _, _ => .alias (.lit false)

def evalStep (w : List Bool) (s : Step) : Bool :=
  ((s.result w.length).val ((⟨s.gates,0⟩ : Circuit).wires w))

theorem combine_correct (w : List Bool) (op : Bool) (a b : Arg) :
    evalStep w (combine op a b) = applyOp op (a.val w) (b.val w) := by
  cases a with
  | lit u => cases b <;> cases u <;> cases op <;> simp [combine,evalStep,applyOp,Arg.val,Step.result,Step.gates,Circuit.wires]
  | wire i =>
    cases b with
    | lit v => cases op <;> cases v <;> simp [combine,evalStep,applyOp,Arg.val,Step.result,Step.gates,Circuit.wires]
    | wire j =>
      rcases Nat.le_total i j with h|h <;> cases op <;>
        simp [combine,evalStep,applyOp,Arg.val,Step.result,Step.gates,Circuit.wires,
          GateOp.eval,h,
          Bool.and_comm,Bool.or_comm]

theorem negate_correct (w : List Bool) (a : Arg) :
    evalStep w (negate a) = !(a.val w) := by
  cases a <;> simp [negate,evalStep,Arg.val,Step.result,Step.gates,Circuit.wires,GateOp.eval]

theorem simplify_correct (w : List Bool) (op : GateOp) (args : List Arg)
    (ops : op = .and ∨ op = .or ∨ op = .not) (small : args.length ≤ 2) :
    evalStep w (simplify op args) = op.eval (args.map (Arg.val w)) := by
  rcases ops with rfl|rfl|rfl <;> cases args with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => first | exact negate_correct w a | simp [simplify,evalStep,Step.result,Step.gates,Circuit.wires,GateOp.eval]
    | cons b tail =>
      cases tail with
      | nil => simp [simplify,combine_correct,negate_correct,GateOp.eval,applyOp]
      | cons c cs => simp at small

theorem cost (s : Step) : s.gates.length ≤ 1 := by cases s <;> simp [Step.gates]

#print axioms simplify_correct

def Arg.valid (cap : Nat) : Arg → Prop
  | .lit _ => True
  | .wire i => i < cap

def Step.valid (cap : Nat) : Step → Prop
  | .alias a => a.valid cap
  | .binary _ i j => i < cap ∧ j < cap
  | .neg i => i < cap

theorem combine_valid {cap : Nat} (op : Bool) {a b : Arg}
    (ha : a.valid cap) (hb : b.valid cap) : (combine op a b).valid cap := by
  cases a with
  | lit x => cases x <;> cases op <;> cases b <;> simp_all [combine,Step.valid,Arg.valid]
  | wire i =>
    cases b with
    | lit y => cases y <;> cases op <;> simp_all [combine,Step.valid,Arg.valid]
    | wire j => exact ⟨ha,hb⟩

theorem simplify_valid (cap : Nat) (op : GateOp) (args : List Arg)
    (ok : ∀ a ∈ args, a.valid cap) : (simplify op args).valid cap := by
  cases op <;> cases args with
  | nil => trivial
  | cons a xs =>
    have ha := ok a (by simp)
    cases xs with
    | nil => first | exact ha | trivial | cases a <;> exact ha
    | cons b bs =>
      have hb := ok b (by simp)
      first | apply combine_valid _ ha hb | trivial | cases a <;> exact ha

def after (w : List Bool) (s : Step) := (⟨s.gates,0⟩ : Circuit).wires w

theorem after_length (w : List Bool) (s : Step) :
    (after w s).length = w.length + s.gates.length := by
  cases s <;> simp [after,Step.gates,Circuit.wires]

theorem old_value (w : List Bool) (s : Step) (a : Arg) (ok : a.valid w.length) :
    a.val (after w s) = a.val w := by
  cases a with
  | lit => rfl
  | wire i =>
    change i < w.length at ok
    cases s <;> simp only [after,Step.gates,Circuit.wires,List.foldl_cons,List.foldl_nil,Arg.val]
    all_goals exact List.getD_append _ _ _ _ ok

theorem result_valid (s : Step) (n : Nat) (h : s.valid n) :
    (s.result n).valid (n+s.gates.length) := by
  cases s <;> simp_all [Step.valid,Step.result,Step.gates,Arg.valid]

structure Program where
  gates : List Gate
  env : List Arg

def translate (cap : Nat) (env : List Arg) : List Gate → Program
  | [] => ⟨[],env⟩
  | g :: gs =>
    let s := simplify g.op (g.inputs.map fun i => env.getD i (.lit false))
    let tail := translate (cap+s.gates.length) (env ++ [s.result cap]) gs
    ⟨s.gates ++ tail.gates, tail.env⟩

theorem translate_size (gs : List Gate) (cap : Nat) (env : List Arg) :
    (translate cap env gs).gates.length ≤ gs.length := by
  induction gs generalizing cap env with
  | nil => simp [translate]
  | cons g gs ih =>
    let s := simplify g.op (g.inputs.map fun i => env.getD i (.lit false))
    have h := ih (cap+s.gates.length) (env ++ [s.result cap])
    have hc := cost s
    change (s.gates ++ (translate (cap+s.gates.length) (env ++ [s.result cap]) gs).gates).length ≤ _
    rw [List.length_append,List.length_cons]
    omega

#print axioms translate_size

def run (gs : List Gate) (w : List Bool) := (⟨gs,0⟩ : Circuit).wires w

private theorem mapped_read (env : List Arg) (w : List Bool) (i : Nat) :
    (env.getD i (.lit false)).val w = (env.map (Arg.val w)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases env[i]? <;> rfl

private theorem read_valid (env : List Arg) (cap i : Nat) (ok : ∀ a ∈ env, a.valid cap) :
    (env.getD i (.lit false)).valid cap := by
  by_cases hi : i < env.length
  · simpa [List.getD_eq_getElem?_getD,hi] using ok env[i] (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    trivial

theorem translate_correct (gs : List Gate) (w : List Bool) (env : List Arg)
    (ok : ∀ a ∈ env, a.valid w.length)
    (allowed : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    let p := translate w.length env gs
    p.env.map (Arg.val (run p.gates w)) = run gs (env.map (Arg.val w)) := by
  induction gs generalizing w env with
  | nil => rfl
  | cons g gs ih =>
    let args := g.inputs.map fun i => env.getD i (.lit false)
    let s := simplify g.op args
    let w' := after w s
    let env' := env ++ [s.result w.length]
    have valid : s.valid w.length := by
      apply simplify_valid
      intro a ha
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      exact read_valid _ _ _ ok
    have hl : w'.length = w.length+s.gates.length := after_length _ _
    have nextOK : ∀ a ∈ env', a.valid w'.length := by
      intro a ha
      rw [hl]
      rcases List.mem_append.mp ha with h|h
      · have h0 := ok a h
        cases a <;> simp_all [Arg.valid]; omega
      · obtain rfl := List.mem_singleton.mp h
        exact result_valid _ _ valid
    have prev : env.map (Arg.val w') = env.map (Arg.val w) :=
      List.map_congr_left (fun a ha => old_value w s a (ok a ha))
    have gateOK := allowed g (by simp)
    have val : (s.result w.length).val w' = g.op.eval (g.inputs.map fun i => (env.map (Arg.val w)).getD i false) := by
      change evalStep w s = _
      rw [show evalStep w s = _ from simplify_correct w g.op args gateOK.1 (by simpa [args] using gateOK.2)]
      simp only [args,List.map_map,Function.comp_def,mapped_read]
    have vals : env'.map (Arg.val w') = env.map (Arg.val w) ++ [g.op.eval (g.inputs.map fun i => (env.map (Arg.val w)).getD i false)] := by
      simp only [env',List.map_append,List.map_cons,List.map_nil,prev,val]
    have hind := ih w' env' nextOK (fun k hk => allowed k (by simp [hk]))
    dsimp only at hind ⊢
    rw [hl,vals] at hind
    simpa only [translate,run,Circuit.wires,List.foldl_append,List.foldl_cons,
      args,s,env',w',after] using hind

#print axioms translate_correct

def inputs (n : Nat) : List Arg := List.ofFn fun k : Fin n => Arg.wire k.val

theorem inputs_valid (n : Nat) : ∀ a ∈ inputs n, a.valid n := by
  intro a ha
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
  exact k.isLt

theorem inputs_values (w : List Bool) : (inputs w.length).map (Arg.val w) = w := by
  apply List.ext_getElem
  · simp [inputs]
  · intro i hi hi'
    simp [inputs,Arg.val,List.getD_eq_getElem?_getD,hi']

/-- For nonconstant circuits the translated output is a wire; all original gates
are covered, including short argument lists and reads of nonexistent wires. -/
theorem eliminate_constants (C : Circuit) (n : Nat)
    (allowed : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (nc : ∃ x y : List Bool, x.length = n ∧ y.length = n ∧ C.eval x ≠ C.eval y) :
    let p := translate n (inputs n) C.gates
    ∃ i : Nat, (⟨p.gates,i⟩ : Circuit).size ≤ C.size ∧
      ∀ x : List Bool, x.length = n → (⟨p.gates,i⟩ : Circuit).eval x = C.eval x := by
  let p := translate n (inputs n) C.gates
  let output := p.env.getD C.output (.lit false)
  have spec (x : List Bool) (hx : x.length = n) : output.val (run p.gates x) = C.eval x := by
    have h := translate_correct C.gates x (inputs n) (hx ▸ inputs_valid n) allowed
    dsimp only at h
    rw [hx] at h
    have hin : (inputs n).map (Arg.val x) = x := hx ▸ inputs_values x
    rw [hin] at h
    change (p.env.getD C.output (.lit false)).val _ = _
    rw [mapped_read]
    exact congrArg (fun xs : List Bool => xs.getD C.output false) h
  cases ho : output with
  | lit v =>
    obtain ⟨x,y,hx,hy,ne⟩ := nc
    have h1 := spec x hx
    have h2 := spec y hy
    rw [ho] at h1 h2
    exact (ne (h1.symm.trans h2)).elim
  | wire i =>
    refine ⟨i,translate_size _ _ _,?_⟩
    intro x hx
    have h := spec x hx
    rw [ho] at h
    exact h

#print axioms eliminate_constants

/-- Parent indices are sorted for AND/OR. NOT has one actual parent. -/
def fits (cap : Nat) (g : Gate) : Prop :=
    (∃ i, i < cap ∧ g.op = .not ∧ g.inputs = [i]) ∨
    (∃ i j, i ≤ j ∧ j < cap ∧ (g.op = .and ∨ g.op = .or) ∧ g.inputs = [i,j])

def FitsFrom (cap : Nat) : List Gate → Prop
  | [] => True
  | g :: gs => fits cap g ∧ FitsFrom (cap+1) gs

theorem translate_fits (gs : List Gate) (cap : Nat) (env : List Arg)
    (ok : ∀ a ∈ env, a.valid cap) : FitsFrom cap (translate cap env gs).gates := by
  induction gs generalizing cap env with
  | nil => trivial
  | cons g gs ih =>
    let s := simplify g.op (g.inputs.map fun i => env.getD i (.lit false))
    have valid : s.valid cap := by
      apply simplify_valid
      intro a ha
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      exact read_valid _ _ _ ok
    have ok' : ∀ a ∈ env ++ [s.result cap], a.valid (cap+s.gates.length) := by
      intro a ha
      rcases List.mem_append.mp ha with h|h
      · have h0 := ok a h
        cases a <;> simp_all [Arg.valid]; omega
      · obtain rfl := List.mem_singleton.mp h
        exact result_valid _ _ valid
    have tail := ih _ _ ok'
    change FitsFrom cap (s.gates ++ (translate (cap+s.gates.length) (env ++ [s.result cap]) gs).gates)
    revert tail valid
    generalize s = step
    intro valid tail
    cases step with
    | «alias» a => exact tail
    | neg i => exact ⟨Or.inl ⟨i,valid,rfl,rfl⟩,tail⟩
    | binary op i j =>
      refine ⟨Or.inr ⟨min i j,max i j,?_,?_,?_,rfl⟩,tail⟩
      · omega
      · exact max_lt valid.1 valid.2
      · cases op <;> simp

#print axioms translate_fits
end Alexrollo64.ConstantPropagation
