-- Equation5789 → Equation17331
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (x ◇ ((y ◇ y) ◇ y)))
-- Conclusion: x = (y ◇ y) ◇ (x ◇ (x ◇ (y ◇ y)))
-- Original submission SHA-256: c3d89076a8027562a26a642b191a3c1c32b5a5f829b652444b72b9d11b12b65f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ ((y ◇ y) ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ y) ◇ (x ◇ (x ◇ (y ◇ y)))
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
  CM.p m.x
    (CM.p m.x
      (CM.p (CM.p m.y m.y) m.y))

abbrev NoRule (a b : CM) :=
  (m : Pat) → a = left m → b = right m → False

def getX : CM → CM
  | CM.p x _ => x
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
      have hx : m.x = q.x := (CM.p.inj hq).1
      exact hx.symm
  | no hn => exact (hn m rfl rfl).elim

theorem op_raw {a b : CM} (h : NoRule a b) : op a b = CM.p a b := by
  unfold op view
  cases hd : detect a b with
  | yes m ha hb => exact (h m ha hb).elim
  | no _ => rfl

theorem no_mismatched_x (y x₁ x₂ tail : CM) (hne : x₁ ≠ x₂) :
    NoRule y (CM.p x₁ (CM.p x₂ tail)) := by
  intro m _ hr
  have h₁ : x₁ = m.x := (CM.p.inj hr).1
  have h₂ : x₂ = m.x := (CM.p.inj (CM.p.inj hr).2).1
  exact hne (h₁.trans h₂.symm)

theorem sz_y_lt_right (m : Pat) : sz m.y < sz (right m) := by
  unfold right
  exact Nat.lt_trans (sz_lt_p_left m.y m.y)
    (Nat.lt_trans
      (sz_lt_p_left (CM.p m.y m.y) m.y)
      (Nat.lt_trans
        (sz_lt_p_right m.x (CM.p (CM.p m.y m.y) m.y))
        (sz_lt_p_right m.x
          (CM.p m.x (CM.p (CM.p m.y m.y) m.y)))))

theorem no_same (t : CM) : NoRule t t := by
  intro m hl hr
  have hself : m.y = right m := hl.symm.trans hr
  exact (Nat.ne_of_lt (sz_y_lt_right m)) (congrArg sz hself)

theorem no_after_square (y : CM) : NoRule (CM.p y y) y := by
  intro m hl hr
  change CM.p y y = m.y at hl
  have h₁ : sz y < sz m.y := by
    rw [← hl]
    exact sz_lt_p_left y y
  have h₂ : sz m.y < sz y := by
    rw [hr]
    exact sz_y_lt_right m
  exact Nat.lt_asymm h₁ h₂

theorem no_after_tail (x y : CM) :
    NoRule x (CM.p (CM.p y y) y) := by
  intro m _ hr
  have hmx : CM.p y y = m.x := (CM.p.inj hr).1
  have hy :
      y = CM.p m.x (CM.p (CM.p m.y m.y) m.y) :=
    (CM.p.inj hr).2
  have h₁ : sz y < sz m.x := by
    rw [← hmx]
    exact sz_lt_p_left y y
  have h₂ : sz m.x < sz y := by
    rw [hy]
    exact sz_lt_p_left m.x (CM.p (CM.p m.y m.y) m.y)
  exact Nat.lt_asymm h₁ h₂

theorem no_after_first_x (x y : CM) :
    NoRule x (CM.p x (CM.p (CM.p y y) y)) := by
  intro m hl hr
  have hx : x = m.x := (CM.p.inj hr).1
  have htail :
      CM.p (CM.p y y) y =
        CM.p m.x (CM.p (CM.p m.y m.y) m.y) :=
    (CM.p.inj hr).2
  have hyy : CM.p y y = m.x := (CM.p.inj htail).1
  have hy : y = CM.p (CM.p m.y m.y) m.y :=
    (CM.p.inj htail).2
  have hpyx : CM.p y y = x := hyy.trans hx.symm
  have h₁ : sz y < sz x := by
    rw [← hpyx]
    exact sz_lt_p_left y y
  have h₂ : sz x < sz y := by
    rw [hl, hy]
    exact Nat.lt_trans (sz_lt_p_left m.y m.y)
      (sz_lt_p_left (CM.p m.y m.y) m.y)
  exact Nat.lt_asymm h₁ h₂

theorem source_holds (x y : CM) :
    x = op y (op x (op x (op (op y y) y))) := by
  rw [op_raw (no_same y)]
  rw [op_raw (no_after_square y)]
  rw [op_raw (no_after_tail x y)]
  rw [op_raw (no_after_first_x x y)]
  exact (op_rule ⟨y, x⟩).symm

theorem target_witness :
    CM.e ≠
      op (op (CM.k CM.e) (CM.k CM.e))
        (op CM.e (op CM.e (op (CM.k CM.e) (CM.k CM.e)))) := by
  decide

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    change x = CM.op y
      (CM.op x (CM.op x (CM.op (CM.op y y) y)))
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e (CM.k CM.e)
    change CM.e =
      CM.op (CM.op (CM.k CM.e) (CM.k CM.e))
        (CM.op CM.e
          (CM.op CM.e (CM.op (CM.k CM.e) (CM.k CM.e)))) at bad
    exact CM.target_witness bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5789_to_17331 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_5789_to_17331
