-- Equation467 → Equation2847
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (x ◇ (y ◇ y)))
-- Conclusion: x = ((x ◇ (x ◇ x)) ◇ x) ◇ x
-- Original submission SHA-256: 9cc6c51d24ba1ead8f8af2fae33637461ea7ae1ec3bf93d0b1714d093704d653
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = ((x ◇ (x ◇ x)) ◇ x) ◇ x
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

def left (m : Pat) : CM :=
  CM.p (CM.p (CM.p m.y m.y) m.x) m.x

def right (m : Pat) : CM := m.y

abbrev NoRule (a b : CM) :=
  (m : Pat) → a = left m → b = right m → False

def getX : CM → CM
  | CM.p (CM.p (CM.p _ _) x) _ => x
  | _ => CM.e

inductive Detect (a b : CM) where
  | yes (m : Pat) (ha : a = left m) (hb : b = right m)
  | no (h : NoRule a b)

def detect (a b : CM) : Detect a b :=
  let m : Pat := ⟨b, getX a⟩
  match cmDecEq a (left m) with
  | isFalse ha => .no (fun q hqa hqb => by
      cases hqa
      cases hqb
      exact ha rfl)
  | isTrue ha =>
      match cmDecEq b (right m) with
      | isFalse hb => .no (fun q hqa hqb => by
          cases hqa
          cases hqb
          exact hb rfl)
      | isTrue hb => .yes m ha hb

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
  | yes q hq _ =>
      change q.x = m.x
      exact (CM.p.inj hq).2.symm
  | no hn => exact (hn m rfl rfl).elim

theorem op_raw {a b : CM} (h : NoRule a b) : op a b = CM.p a b := by
  unfold op view
  cases hd : detect a b with
  | yes m ha hb => exact (h m ha hb).elim
  | no _ => rfl

theorem sz_y_lt_left (m : Pat) : sz m.y < sz (left m) := by
  unfold left
  exact Nat.lt_trans
    (sz_lt_p_left m.y m.y)
    (Nat.lt_trans
      (sz_lt_p_left (CM.p m.y m.y) m.x)
      (sz_lt_p_left (CM.p (CM.p m.y m.y) m.x) m.x))

theorem no_same (t : CM) : NoRule t t := by
  intro m hl hr
  have ht : t = m.y := by simpa [right] using hr
  have hself : m.y = left m := ht.symm.trans hl
  exact (Nat.ne_of_lt (sz_y_lt_left m)) (congrArg sz hself)

theorem no_square_x (y x : CM) :
    NoRule (CM.p y y) x := by
  intro m hl _
  have hself :
      m.x = CM.p (CM.p m.y m.y) m.x :=
    (CM.p.inj hl).2.symm.trans (CM.p.inj hl).1
  exact
    (Nat.ne_of_lt
      (sz_lt_p_right (CM.p m.y m.y) m.x))
      (congrArg sz hself)

theorem no_middle (y x : CM) :
    NoRule (CM.p (CM.p y y) x) x := by
  intro m hl hr
  have hxY : x = m.y := by simpa [right] using hr
  have hxX : x = m.x := (CM.p.inj hl).2
  have hinner :
      CM.p y y = CM.p (CM.p m.y m.y) m.x :=
    (CM.p.inj hl).1
  have hyP : y = CM.p m.y m.y := (CM.p.inj hinner).1
  have hyX : y = m.x := (CM.p.inj hinner).2
  have hmy_y : m.y = y :=
    (hxY.symm.trans hxX).trans hyX.symm
  have hself : m.y = CM.p m.y m.y :=
    hmy_y.trans hyP
  exact
    (Nat.ne_of_lt (sz_lt_p_left m.y m.y))
      (congrArg sz hself)

theorem source_holds (x y : CM) :
    x = op (op (op (op y y) x) x) y := by
  rw [op_raw (no_same y)]
  rw [op_raw (no_square_x y x)]
  rw [op_raw (no_middle y x)]
  exact (op_rule ⟨y, x⟩).symm

theorem no_left_e (b : CM) : NoRule CM.e b := by
  intro m hl _
  exact CM.noConfusion hl

theorem no_left_k (a b : CM) : NoRule (CM.k a) b := by
  intro m hl _
  exact CM.noConfusion hl

theorem no_A_B :
    NoRule
      (CM.p (CM.k CM.e) CM.e)
      (CM.p (CM.k CM.e) (CM.k CM.e)) := by
  intro m hl _
  exact CM.noConfusion (CM.p.inj hl).1

theorem no_C_D :
    NoRule
      (CM.p
        (CM.p (CM.k CM.e) CM.e)
        (CM.p (CM.k CM.e) (CM.k CM.e)))
      (CM.p CM.e (CM.k CM.e)) := by
  intro m hl _
  exact CM.noConfusion (CM.p.inj (CM.p.inj hl).1).1

end CM

end submission

open submission

open submission

def submission.oppositeMagma3140 : Magma CM where
  op a b := CM.op b a

def submission : Goal := by
  refine ⟨CM, oppositeMagma3140, ?_, ?_⟩
  · intro x y
    change x = CM.op (CM.op (CM.op (CM.op y y) x) x) y
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e
    nomatch bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_467_to_2847 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_467_to_2847
