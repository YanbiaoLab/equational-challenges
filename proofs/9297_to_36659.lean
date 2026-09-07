-- Equation9297 → Equation36659
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ x) ◇ (y ◇ (y ◇ y)))
-- Conclusion: x = (((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇ y
-- Original submission SHA-256: 585db262038d4b71644808f3cae42a81376cf621379f2ea3dd3d70e6f0fa5746
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ x) ◇ (y ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (((y ◇ y) ◇ y) ◇ (x ◇ x)) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   

set_option maxRecDepth 10000

namespace submission

inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM

namespace CM

def cmDecEq : (a b : CM) → Decidable (a = b)
  | CM.e, CM.e => isTrue rfl
  | CM.e, CM.k _ => isFalse (fun h => CM.noConfusion h)
  | CM.e, CM.p _ _ => isFalse (fun h => CM.noConfusion h)
  | CM.k _, CM.e => isFalse (fun h => CM.noConfusion h)
  | CM.p _ _, CM.e => isFalse (fun h => CM.noConfusion h)
  | CM.k a, CM.k b =>
      match cmDecEq a b with
      | isTrue h => isTrue (congrArg CM.k h)
      | isFalse h => isFalse (fun hab => h (CM.k.inj hab))
  | CM.k _, CM.p _ _ => isFalse (fun h => CM.noConfusion h)
  | CM.p _ _, CM.k _ => isFalse (fun h => CM.noConfusion h)
  | CM.p a b, CM.p c d =>
      match cmDecEq a c with
      | isFalse h => isFalse (fun hab => h (CM.p.inj hab).1)
      | isTrue hac =>
          match cmDecEq b d with
          | isFalse h => isFalse (fun hab => h (CM.p.inj hab).2)
          | isTrue hbd => isTrue (by cases hac; cases hbd; rfl)

instance instDecidableEq : DecidableEq CM := cmDecEq

def sz : CM → Nat
  | CM.e => 0
  | CM.k x => sz x + 1
  | CM.p x y => (sz x + 1) + (sz y + 1)

theorem sz_lt_p_left (a b : CM) : sz a < sz (CM.p a b) := by
  change sz a < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))

theorem sz_lt_p_right (a b : CM) : sz b < sz (CM.p a b) := by
  change sz b < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz b))
    (Nat.le_add_left (sz b + 1) (sz a + 1))

structure Pat where
  y : CM
  x : CM

def left (m : Pat) : CM := m.y

def right (m : Pat) : CM :=
  CM.p (CM.p m.x m.x) (CM.p m.y (CM.p m.y m.y))

abbrev NoRule (a b : CM) :=
  (m : Pat) → a = left m → b = right m → False

def getX : CM → CM
  | CM.p (CM.p x _) _ => x
  | _ => CM.e

inductive Detect (a b : CM) where
  | yes (m : Pat) (ha : a = left m) (hb : b = right m)
  | no (h : NoRule a b)

def detect (a b : CM) : Detect a b :=
  let m : Pat := ⟨a, getX b⟩
  -- This whole equality checks both occurrences of `x`, not only the one
  -- extracted by `getX`.
  match cmDecEq b (right m) with
  | isFalse hb => .no (fun q hqa hqb => by
      cases hqa
      cases hqb
      exact hb rfl)
  | isTrue hb => .yes m rfl hb

inductive View (a b : CM) where
  | rule (m : Pat) (ha : a = left m) (hb : b = right m)
  | raw (h : NoRule a b)

def view (a b : CM) : View a b :=
  match detect a b with
  | .yes m ha hb => .rule m ha hb
  | .no h => .raw h

def op (a b : CM) : CM :=
  match view a b with
  | .rule m _ _ => m.x
  | .raw _ => CM.p a b

instance instMagma : Magma CM where
  op := op

theorem op_rule (m : Pat) : op (left m) (right m) = m.x := by
  unfold op view
  cases hd : detect (left m) (right m) with
  | yes q _ hq =>
      change q.x = m.x
      have hx : m.x = q.x :=
        (CM.p.inj (CM.p.inj hq).1).1
      exact hx.symm
  | no hn => exact (hn m rfl rfl).elim

theorem op_raw {a b : CM} (h : NoRule a b) : op a b = CM.p a b := by
  unfold op view
  cases hd : detect a b with
  | yes m ha hb => exact (h m ha hb).elim
  | no _ => rfl

theorem no_same (t : CM) : NoRule t t := by
  intro m hl hr
  have hself : m.y = right m := hl.symm.trans hr
  have hlt : sz m.y < sz (right m) := by
    unfold right
    exact Nat.lt_trans
      (sz_lt_p_left m.y m.y)
      (Nat.lt_trans
        (sz_lt_p_right m.y (CM.p m.y m.y))
        (sz_lt_p_right
          (CM.p m.x m.x)
          (CM.p m.y (CM.p m.y m.y))))
  exact (Nat.ne_of_lt hlt) (congrArg sz hself)

theorem no_y_square (y : CM) : NoRule y (CM.p y y) := by
  intro m hl hr
  have hy0 : y = m.y := by simpa [left] using hl
  have hy1 : y = CM.p m.y (CM.p m.y m.y) :=
    (CM.p.inj hr).2
  have hself : m.y = CM.p m.y (CM.p m.y m.y) :=
    hy0.symm.trans hy1
  exact
    (Nat.ne_of_lt (sz_lt_p_left m.y (CM.p m.y m.y)))
      (congrArg sz hself)

theorem no_xx_y_y_square (x y : CM) :
    NoRule (CM.p x x) (CM.p y (CM.p y y)) := by
  intro m _ hr
  have htail :
      CM.p y y = CM.p m.y (CM.p m.y m.y) :=
    (CM.p.inj hr).2
  have hy1 : y = m.y := (CM.p.inj htail).1
  have hy2 : y = CM.p m.y m.y := (CM.p.inj htail).2
  have hself : m.y = CM.p m.y m.y := hy1.symm.trans hy2
  exact (Nat.ne_of_lt (sz_lt_p_left m.y m.y)) (congrArg sz hself)

theorem source_holds (x y : CM) :
    x = op y (op (op x x) (op y (op y y))) := by
  rw [op_raw (no_same x)]
  rw [op_raw (no_same y)]
  rw [op_raw (no_y_square y)]
  rw [op_raw (no_xx_y_y_square x y)]
  exact (op_rule ⟨y, x⟩).symm

theorem no_right_e (a : CM) : NoRule a CM.e := by
  intro m _ hr
  exact CM.noConfusion hr

theorem no_right_k (a b : CM) : NoRule a (CM.k b) := by
  intro m _ hr
  exact CM.noConfusion hr

theorem no_tail_e2 (a b : CM) :
    NoRule a (CM.p b CM.e) := by
  intro m _ hr
  exact CM.noConfusion (CM.p.inj hr).2

theorem raw_right_e (a : CM) : op a CM.e = CM.p a CM.e :=
  op_raw (no_right_e a)

theorem raw_right_k (a b : CM) :
    op a (CM.k b) = CM.p a (CM.k b) :=
  op_raw (no_right_k a b)

theorem raw_tail_e2 (a b : CM) :
    op a (CM.p b CM.e) = CM.p a (CM.p b CM.e) :=
  op_raw (no_tail_e2 a b)

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    change x =
      CM.op y (CM.op (CM.op x x) (CM.op y (CM.op y y)))
    exact CM.source_holds x y
  · intro target
    let K : CM := CM.k CM.e
    have bad := target CM.e K
    change CM.e =
      CM.op
        (CM.op (CM.op (CM.op K K) K) (CM.op CM.e CM.e))
        K at bad
    rw [CM.raw_right_k K CM.e] at bad
    rw [CM.raw_right_k (CM.p K K) CM.e] at bad
    rw [CM.raw_right_e CM.e] at bad
    rw [CM.raw_tail_e2
      (CM.p (CM.p K K) K) CM.e] at bad
    rw [CM.raw_right_k
      (CM.p (CM.p (CM.p K K) K) (CM.p CM.e CM.e))
      CM.e] at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9297_to_36659 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_9297_to_36659
