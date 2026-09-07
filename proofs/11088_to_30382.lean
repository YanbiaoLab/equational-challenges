-- Equation11088 → Equation30382
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))
-- Conclusion: x = (y ◇ (x ◇ ((y ◇ y) ◇ y))) ◇ y
-- Original submission SHA-256: 240f66a9c895f276468aefe0e1ec15ac78a939352192cf27294a030db1386d6b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (x ◇ ((y ◇ y) ◇ y))) ◇ y
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

def square (m : Pat) : CM := CM.p m.y m.y

def right (m : Pat) : CM :=
  CM.p (CM.p m.x (square m)) (square m)

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
      have hx : m.x = q.x := (CM.p.inj (CM.p.inj hq).1).1
      exact hx.symm
  | no hn => exact (hn m rfl rfl).elim

theorem op_raw {a b : CM} (h : NoRule a b) : op a b = CM.p a b := by
  unfold op view
  cases hd : detect a b with
  | yes m ha hb => exact (h m ha hb).elim
  | no _ => rfl

theorem sz_y_lt_right (m : Pat) : sz m.y < sz (right m) := by
  unfold right square
  exact Nat.lt_trans
    (sz_lt_p_left m.y m.y)
    (sz_lt_p_right
      (CM.p m.x (CM.p m.y m.y))
      (CM.p m.y m.y))

theorem no_same (t : CM) : NoRule t t := by
  intro m hl hr
  have hself : m.y = right m := by
    simpa [left] using hl.symm.trans hr
  exact (Nat.ne_of_lt (sz_y_lt_right m)) (congrArg sz hself)

theorem no_right_square (a y : CM) :
    NoRule a (CM.p y y) := by
  intro m _ hr
  have hfirst :
      y = CM.p m.x (CM.p m.y m.y) := by
    simpa [right, square] using (CM.p.inj hr).1
  have hsecond : y = CM.p m.y m.y := by
    simpa [right, square] using (CM.p.inj hr).2
  have hpair :
      CM.p m.x (CM.p m.y m.y) = CM.p m.y m.y :=
    hfirst.symm.trans hsecond
  have hself : CM.p m.y m.y = m.y := (CM.p.inj hpair).2
  exact
    (Nat.ne_of_lt (sz_lt_p_left m.y m.y))
      (congrArg sz hself.symm)

theorem source_holds (x y : CM) :
    x = op y (op (op x (op y y)) (op y y)) := by
  let P : CM := CM.p y y
  let A : CM := CM.p x P
  have h0 : op y y = P := by
    change op y y = CM.p y y
    exact op_raw (no_same y)
  have h1 : op x (op y y) = A := by
    calc
      op x (op y y) = op x P := congrArg (op x) h0
      _ = CM.p x P := op_raw (no_right_square x y)
  have h2 :
      op (op x (op y y)) (op y y) = right ⟨y, x⟩ := by
    calc
      op (op x (op y y)) (op y y) = op A (op y y) :=
        congrArg (fun q => op q (op y y)) h1
      _ = op A P := congrArg (op A) h0
      _ = CM.p A P := op_raw (no_right_square A y)
  exact
    (op_rule ⟨y, x⟩).symm.trans
      (congrArg (op y) h2.symm)

theorem no_right_k (a b : CM) : NoRule a (CM.k b) := by
  intro m _ hr
  exact CM.noConfusion hr

theorem no_tail_k (a b c : CM) :
    NoRule a (CM.p b (CM.k c)) := by
  intro m _ hr
  exact CM.noConfusion (CM.p.inj hr).2

theorem no_K_U :
    NoRule
      (CM.k CM.e)
      (CM.p
        CM.e
        (CM.p
          (CM.p (CM.k CM.e) (CM.k CM.e))
          (CM.k CM.e))) := by
  intro m _ hr
  have htail :
      CM.p
          (CM.p (CM.k CM.e) (CM.k CM.e))
          (CM.k CM.e) =
        CM.p m.y m.y := by
    simpa [right, square] using (CM.p.inj hr).2
  have hS :
      CM.p (CM.k CM.e) (CM.k CM.e) = m.y :=
    (CM.p.inj htail).1
  have hK : CM.k CM.e = m.y := (CM.p.inj htail).2
  exact CM.noConfusion (hS.trans hK.symm)

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    change x = CM.op y
      (CM.op (CM.op x (CM.op y y)) (CM.op y y))
    exact CM.source_holds x y
  · intro target
    let K : CM := CM.k CM.e
    let S : CM := CM.p K K
    let T : CM := CM.p S K
    let U : CM := CM.p CM.e T
    let V : CM := CM.p K U
    let W : CM := CM.p V K
    have bad := target CM.e K
    change CM.e =
      CM.op
        (CM.op K (CM.op CM.e (CM.op (CM.op K K) K)))
        K at bad
    rw [CM.op_raw (CM.no_same K)] at bad
    change CM.e = CM.op (CM.op K (CM.op CM.e (CM.op S K))) K at bad
    rw [CM.op_raw (CM.no_right_k S CM.e)] at bad
    change CM.e = CM.op (CM.op K (CM.op CM.e T)) K at bad
    rw [CM.op_raw (CM.no_tail_k CM.e S CM.e)] at bad
    change CM.e = CM.op (CM.op K U) K at bad
    rw [CM.op_raw CM.no_K_U] at bad
    change CM.e = CM.op V K at bad
    rw [CM.op_raw (CM.no_right_k V CM.e)] at bad
    change CM.e = W at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11088_to_30382 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_11088_to_30382
