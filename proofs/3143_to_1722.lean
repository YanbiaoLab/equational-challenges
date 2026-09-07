-- Equation3143 → Equation1722
-- Recorded verdict: false
-- Premise: x = (((y ◇ y) ◇ x) ◇ y) ◇ y
-- Conclusion: x = (y ◇ y) ◇ ((x ◇ y) ◇ y)
-- Original submission SHA-256: ba57e431f4e7e8afd010db6f769388509c5020d1fcdbc13f63df6c1c4b5cd8ef
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (((y ◇ y) ◇ x) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ y) ◇ ((x ◇ y) ◇ y)
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

lemma sz_lt_p_left (a b : CM) : sz a < sz (CM.p a b) := by
  change sz a < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))

lemma sz_lt_p_right (a b : CM) : sz b < sz (CM.p a b) := by
  change sz b < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz b))
    (Nat.le_add_left (sz b + 1) (sz a + 1))

structure Pat where
  y : CM
  x : CM

def left (m : Pat) : CM := CM.p (CM.p (CM.p m.y m.y) m.x) m.y
def right (m : Pat) : CM := m.y

abbrev No (a b : CM) :=
  (m : Pat) → a = left m → b = right m → False

def getX : CM → CM
  | CM.p (CM.p (CM.p _ _) x) _ => x
  | _ => CM.e

inductive Detect (a b : CM) where
  | yes (m : Pat) (ha : a = left m) (hb : b = right m)
  | no (h : No a b)

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
  | raw (h : No a b)

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

lemma op_rule (m : Pat) : op (left m) (right m) = m.x := by
  unfold op view
  cases hd : detect (left m) (right m) with
  | yes q hq _ =>
      change q.x = m.x
      have hx : m.x = q.x := (CM.p.inj (CM.p.inj hq).1).2
      exact hx.symm
  | no hn => exact (hn m rfl rfl).elim

lemma op_raw {a b : CM} (h : No a b) : op a b = CM.p a b := by
  unfold op view
  cases hd : detect a b with
  | yes m ha hb => exact (h m ha hb).elim
  | no _ => rfl

lemma no_same (t : CM) : No t t := by
  intro m hl hr
  have ht : t = m.y := by simpa [right] using hr
  have hself : m.y = left m := ht.symm.trans hl
  have hlt : sz m.y < sz (left m) := by
    unfold left
    exact Nat.lt_trans (sz_lt_p_left m.y m.y)
      (Nat.lt_trans
        (sz_lt_p_left (CM.p m.y m.y) m.x)
        (sz_lt_p_left (CM.p (CM.p m.y m.y) m.x) m.y))
  exact (Nat.ne_of_lt hlt) (congrArg sz hself)

lemma no_after_square (y x : CM) : No (CM.p y y) x := by
  intro m hl _
  have hy1 : y = CM.p (CM.p m.y m.y) m.x := (CM.p.inj hl).1
  have hy2 : y = m.y := (CM.p.inj hl).2
  have hself : m.y = CM.p (CM.p m.y m.y) m.x := hy2.symm.trans hy1
  have hlt : sz m.y < sz (CM.p (CM.p m.y m.y) m.x) :=
    Nat.lt_trans (sz_lt_p_left m.y m.y)
      (sz_lt_p_left (CM.p m.y m.y) m.x)
  exact (Nat.ne_of_lt hlt) (congrArg sz hself)

lemma no_after_middle (y x : CM) : No (CM.p (CM.p y y) x) y := by
  intro m hl hr
  have hy : y = m.y := by simpa [right] using hr
  have hfirst :
      CM.p y y = CM.p (CM.p m.y m.y) m.x := (CM.p.inj hl).1
  have hleft : y = CM.p m.y m.y := (CM.p.inj hfirst).1
  have hself : m.y = CM.p m.y m.y := hy.symm.trans hleft
  exact (Nat.ne_of_lt (sz_lt_p_left m.y m.y)) (congrArg sz hself)

lemma source_holds (x y : CM) :
    x = op (op (op (op y y) x) y) y := by
  rw [op_raw (no_same y)]
  rw [op_raw (no_after_square y x)]
  rw [op_raw (no_after_middle y x)]
  exact (op_rule ⟨y, x⟩).symm

lemma no_left_e (b : CM) : No CM.e b := by
  intro m h _
  exact CM.noConfusion h

lemma no_left_k (a b : CM) : No (CM.k a) b := by
  intro m h _
  exact CM.noConfusion h

lemma no_B_K :
    No (CM.p CM.e (CM.k CM.e)) (CM.k CM.e) := by
  intro m h _
  exact CM.noConfusion (CM.p.inj h).1

lemma no_A_C :
    No
      (CM.p (CM.k CM.e) (CM.k CM.e))
      (CM.p (CM.p CM.e (CM.k CM.e)) (CM.k CM.e)) := by
  intro m hl hr
  have hk : CM.k CM.e = m.y := (CM.p.inj hl).2
  have hc :
      CM.p (CM.p CM.e (CM.k CM.e)) (CM.k CM.e) = m.y := by
    simpa [right] using hr
  exact CM.noConfusion (hc.trans hk.symm)

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    change x = CM.op (CM.op (CM.op (CM.op y y) x) y) y
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e (CM.k CM.e)
    change
      CM.e =
        CM.op
          (CM.op (CM.k CM.e) (CM.k CM.e))
          (CM.op (CM.op CM.e (CM.k CM.e)) (CM.k CM.e)) at bad
    have hA :
        CM.op (CM.k CM.e) (CM.k CM.e) =
          CM.p (CM.k CM.e) (CM.k CM.e) :=
      CM.op_raw (CM.no_left_k CM.e (CM.k CM.e))
    have hB :
        CM.op CM.e (CM.k CM.e) = CM.p CM.e (CM.k CM.e) :=
      CM.op_raw (CM.no_left_e (CM.k CM.e))
    have hC :
        CM.op (CM.p CM.e (CM.k CM.e)) (CM.k CM.e) =
          CM.p (CM.p CM.e (CM.k CM.e)) (CM.k CM.e) :=
      CM.op_raw CM.no_B_K
    have hD :
        CM.op
            (CM.p (CM.k CM.e) (CM.k CM.e))
            (CM.p (CM.p CM.e (CM.k CM.e)) (CM.k CM.e)) =
          CM.p
            (CM.p (CM.k CM.e) (CM.k CM.e))
            (CM.p (CM.p CM.e (CM.k CM.e)) (CM.k CM.e)) :=
      CM.op_raw CM.no_A_C
    rw [hA, hB, hC, hD] at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3143_to_1722 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_3143_to_1722
