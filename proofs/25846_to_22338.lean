-- Equation25846 → Equation22338
-- Recorded verdict: false
-- Premise: x = (x ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ y)
-- Conclusion: x = (x ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ y)
-- Original submission SHA-256: 92e5a6fdbcf1467305c1f113f6789961b13e73b0923115ab0b3fa5c8425aca6a
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

-- Embedded module: JudgeMagma.Magma
section
/- Magma class, ◇ notation, and helpers for building finite magmas. -/

class Magma (α : Type _) where
  /-- The binary magma operation, written `◇`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

/-- Build a `Magma (Fin n)` from a flat list of values.
    Entry at index `i*n + j` gives the result of `i ◇ j`.
    Usage: `instance : Magma (Fin 3) := magmaFin 3 [0,0,0, 0,0,0, 0,0,1]`

    Marked `@[implicit_reducible]` because Lean 4.32 requires class-valued
    definitions to be transparent to instance resolution. Deliberately not
    plain `@[reducible]`: that would unfold the table literal during general
    unification too, which is pure cost for the large `Fin n` tables here. -/
@[implicit_reducible]
def magmaFin (n : Nat) (table : List Nat) : Magma (Fin n) where
  op a b :=
    let idx := a.val * n + b.val
    ⟨table[idx]! % n, Nat.mod_lt _ (Fin.pos a)⟩
end

-- Embedded module: JudgeProblem
section
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace submission
inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM
deriving DecidableEq
namespace CM
def eqb : CM → CM → Bool
  | e, e => true
  | e, k _ => false
  | e, p _ _ => false
  | k _, e => false
  | k a, k b => eqb a b
  | k _, p _ _ => false
  | p _ _, e => false
  | p _ _, k _ => false
  | p a b, p c d =>
      match eqb a c with
      | true => eqb b d
      | false => false
theorem band_true : {a b : Bool} → (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | false, _, h => Bool.noConfusion h
  | true, false, h => Bool.noConfusion h
theorem eqb_self : (a : CM) → eqb a a = true
  | e => rfl
  | k a => eqb_self a
  | p a b => by rw [eqb, eqb_self a, eqb_self b]
theorem eqb_eq : {a b : CM} → eqb a b = true → a = b
  | e, e, _ => rfl
  | e, k _, h => Bool.noConfusion h
  | e, p _ _, h => Bool.noConfusion h
  | k _, e, h => Bool.noConfusion h
  | k a, k b, h => congrArg k (eqb_eq h)
  | k _, p _ _, h => Bool.noConfusion h
  | p _ _, e, h => Bool.noConfusion h
  | p _ _, k _, h => Bool.noConfusion h
  | p a b, p c d, h => by
      change (match eqb a c with | true => eqb b d | false => false) = true at h
      cases q : eqb a c with
      | false =>
        rw [q] at h
        exact Bool.noConfusion h
      | true =>
        rw [q] at h
        exact congrArg (fun z => p z b) (eqb_eq q) |>.trans
          (congrArg (fun z => p c z) (eqb_eq h))
def L : CM → CM | e => e | k _ => e | p a _ => a
def R : CM → CM | e => e | k _ => e | p _ b => b
def U : CM → CM | e => e | k a => a | p _ _ => e
def sz : CM → Nat
  | e => 0
  | k a => sz a + 1
  | p a b => (sz a + 1) + (sz b + 1)
theorem sz_lt_p_left (a b : CM) : sz a < sz (p a b) := by
  change sz a < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))
theorem sz_lt_p_right (a b : CM) : sz b < sz (p a b) := by
  change sz b < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz b))
    (Nat.le_add_left (sz b + 1) (sz a + 1))
structure Pat where
  x : CM
  y : CM
def left (m : Pat) : CM := (p m.x (p (p m.y m.y) m.y))
def right (m : Pat) : CM := (p m.y m.y)
abbrev NoRule (a b : CM) :=
  (m : Pat) → a = left m → b = right m → False
def get_x (a b : CM) : CM := (L a)
def get_y (a b : CM) : CM := (L (L (R a)))
def candidate (a b : CM) : Pat := ⟨get_x a b, get_y a b⟩
def op (a b : CM) : CM :=
  let m := candidate a b
  match eqb a (left m) && eqb b (right m) with
  | true => m.x
  | false => p a b
instance instMagma : Magma CM where op := op
theorem op_rule (m : Pat) : op (left m) (right m) = m.x := by
  unfold op
  change (match eqb (left m) (left m) && eqb (right m) (right m) with
    | true => m.x | false => _) = m.x
  rw [eqb_self, eqb_self]
  rfl
theorem op_raw {a b : CM} (h : NoRule a b) : op a b = p a b := by
  unfold op
  change (match eqb a (left (candidate a b)) && eqb b (right (candidate a b)) with
    | true => (candidate a b).x | false => p a b) = p a b
  cases yes : eqb a (left (candidate a b)) && eqb b (right (candidate a b)) with
  | false => rfl
  | true =>
    have q := band_true yes
    exact (h (candidate a b) (eqb_eq q.1) (eqb_eq q.2)).elim
theorem no0 (x y : CM) :
    NoRule y y := by
  intro m ha hb
  have e0 := congrArg (fun q => q) ha
  change y = (p m.x (p (p m.y m.y) m.y)) at e0
  have e1 := congrArg (fun q => q) hb
  change y = (p m.y m.y) at e1
  have cut := congrArg (fun q => (R q)) (Eq.trans (Eq.symm (Eq.trans (e1) (rfl))) (Eq.trans e0 (rfl)))
  change m.y = (p (p m.y m.y) m.y) at cut
  have cyc : m.y = (p (p m.y m.y) m.y) := by
    exact cut
  have hlt : sz m.y < sz (p (p m.y m.y) m.y) := by
    exact Nat.lt_trans (sz_lt_p_left m.y m.y) (sz_lt_p_left (p m.y m.y) m.y)
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem no1 (x y : CM) :
    NoRule (p y y) y := by
  intro m ha hb
  have e0 := congrArg (fun q => (L q)) ha
  change y = m.x at e0
  have e1 := congrArg (fun q => (R q)) ha
  change y = (p (p m.y m.y) m.y) at e1
  have e2 := congrArg (fun q => q) hb
  change y = (p m.y m.y) at e2
  have cut := congrArg (fun q => (L q)) (Eq.trans (Eq.symm (Eq.trans (e2) (rfl))) (Eq.trans e1 (rfl)))
  change m.y = (p m.y m.y) at cut
  have cyc : m.y = (p m.y m.y) := by
    exact cut
  have hlt : sz m.y < sz (p m.y m.y) := by
    exact sz_lt_p_left m.y m.y
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem no2 (x y : CM) :
    NoRule x (p (p y y) y) := by
  intro m ha hb
  have e0 := congrArg (fun q => q) ha
  change x = (p m.x (p (p m.y m.y) m.y)) at e0
  have e1 := congrArg (fun q => (L q)) hb
  change (p y y) = m.y at e1
  have e2 := congrArg (fun q => (R q)) hb
  change y = m.y at e2
  have cyc : m.y = (p m.y m.y) := by
    exact Eq.symm (Eq.trans (Eq.symm (Eq.trans (congrArg (fun z => p z y) (Eq.trans (e2) (rfl))) (congrArg (fun z => p m.y z) (Eq.trans (e2) (rfl))))) (Eq.trans e1 (rfl)))
  have hlt : sz m.y < sz (p m.y m.y) := by
    exact sz_lt_p_left m.y m.y
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x y : CM) :
    x = (op (op x (op (op y y) y)) (op y y)) := by
  rw [op_raw (no0 x y)]
  rw [op_raw (no1 x y)]
  rw [op_raw (no2 x y)]
  exact (op_rule ({ x := x, y := y })).symm
end CM
end submission
open submission
open submission.CM
def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    change x = (op (op x (op (op y y) y)) (op y y))
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e CM.e
    change CM.e = (CM.p (CM.p CM.e (CM.p CM.e CM.e)) (CM.p (CM.p CM.e CM.e) CM.e)) at bad
    exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => false | p _ _ => true) bad)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25846_to_22338 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_25846_to_22338
