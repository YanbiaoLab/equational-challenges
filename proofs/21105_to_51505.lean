-- Equation21105 → Equation51505
-- Recorded verdict: false
-- Premise: x = (y ◇ z) ◇ (((y ◇ z) ◇ z) ◇ x)
-- Conclusion: x ◇ y = ((x ◇ z) ◇ (w ◇ x)) ◇ y
-- Original submission SHA-256: c2aa3d21b8ea5aa40ad054a9d55aa4ff46a4301584174bc1af853fa213c447b3
-- Aurora-accepted correction SHA-256: bf12fe0f61cc366ab4f2a85c44c445a04181cb3d2bcd8ea96d3120b6c9cf59fb
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (((y ◇ z) ◇ z) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((x ◇ z) ◇ (w ◇ x)) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace DerivedParity

inductive V where
  | zero
  | odd (n : Nat)
  | even (n : Nat)
  deriving DecidableEq

def color : V → Bool
  | .zero | .even _ => false
  | .odd _ => true

def step : V → Bool → V
  | .zero, false => .zero
  | .odd n, false => .even n
  | .even n, false => .odd n
  | .zero, true => .odd 0
  | .odd 0, true => .zero
  | .odd (n + 1), true => .even n
  | .even n, true => .odd (n + 1)

def op (x y : V) : V := step x (color y)

theorem right_congr (a b c : V) (h : color b = color c) :
    op a b = op a c := by
  simp [op, h]

theorem involutive (a b : V) : op (op a b) b = a := by
  cases a with
  | zero => cases h : color b <;> simp [op, step, h]
  | odd n =>
      cases n with
      | zero => cases h : color b <;> simp [op, step, h]
      | succ n => cases h : color b <;> simp [op, step, h]
  | even n => cases h : color b <;> simp [op, step, h]

theorem right_color (a b : V) : color (op (op a b) a) = color a := by
  simp only [op]
  cases a with
  | zero => cases h : color b <;> rfl
  | odd n =>
      cases n with
      | zero => cases h : color b <;> rfl
      | succ n => cases h : color b <;> rfl
  | even n => cases h : color b <;> rfl

theorem source2481 (x y z : V) :
    x = op (op x (op (op y z) y)) y := by
  rw [right_congr x (op (op y z) y) y (right_color y z)]
  exact (involutive x y).symm

theorem stable_color (a b : V) :
    color (op a (op a b)) = color (op a b) := by
  simp only [op]
  cases a with
  | zero => cases h : color b <;> rfl
  | odd n =>
      cases n with
      | zero => cases h : color b <;> rfl
      | succ n => cases h : color b <;> rfl
  | even n => cases h : color b <;> rfl

def opp (x y : V) : V := op y x

theorem source21105 (x y z : V) :
    x = opp (opp y z) (opp (opp (opp y z) z) x) := by
  simp only [opp]
  rw [right_congr x (op z (op z y)) (op z y) (stable_color z y)]
  exact (involutive x (op z y)).symm

theorem source24673 (x y z : V) :
    x = opp (opp (opp y z) z) (opp (opp y z) x) := by
  simp only [opp]
  rw [right_congr x (op z y) (op z (op z y)) (stable_color z y).symm]
  exact (involutive x (op z (op z y))).symm

theorem target54178_not :
    ¬ ∀ x y z : V,
      op x (op y y) = op x (op y (op z y)) := by
  intro h
  have bad := h .zero .zero (.even 0)
  exact (by decide :
    op .zero (op .zero .zero) ≠
      op .zero (op .zero (op (.even 0) .zero))) bad

theorem source32030 (x y z : V) :
    x = op (op x (op (op y (op z y)) y)) y :=
  source2481 x y (op z y)

theorem target43297_not :
    ¬ ∀ x y z w : V,
      op x x = op x (op (op x y) (op z w)) := by
  intro h
  exact (by decide :
    op .zero .zero ≠
      op .zero (op (op .zero .zero) (op (.even 0) .zero)))
    (h .zero .zero (.even 0) .zero)

theorem target44436_not :
    ¬ ∀ x y z w u : V,
      op x y = op x (op (op y (op z w)) u) := by
  intro h
  exact (by decide :
    op .zero (.odd 0) ≠
      op .zero (op (op (.odd 0) (op (.even 0) .zero)) .zero))
    (h .zero (.odd 0) (.even 0) .zero .zero)

theorem target14757_not :
    ¬ ∀ x y z : V,
      x = opp y (opp (opp (opp y y) (opp z y)) x) := by
  intro h
  exact (by decide :
    (.zero : V) ≠
      opp (.odd 0) (opp (opp (opp (.odd 0) (.odd 0))
        (opp (.odd 0) (.odd 0))) .zero))
    (h .zero (.odd 0) (.odd 0))

theorem target1742_not :
    ¬ ∀ x y z : V,
      x = opp (opp y y) (opp (opp z y) x) := by
  intro h
  exact (by decide :
    (.zero : V) ≠
      opp (opp .zero .zero) (opp (opp (.odd 0) .zero) .zero))
    (h .zero .zero (.odd 0))

theorem target24818_not :
    ¬ ∀ x y z w : V,
      x = opp (opp (opp y z) w) (opp (opp w w) x) := by
  intro h
  exact (by decide :
    (.zero : V) ≠
      opp (opp (opp .zero (.even 0)) .zero)
        (opp (opp .zero .zero) .zero))
    (h .zero .zero (.even 0) .zero)

theorem target51505_not :
    ¬ ∀ x y z w : V,
      opp x y = opp (opp (opp x z) (opp w x)) y := by
  intro h
  exact (by decide :
    opp .zero .zero ≠
      opp (opp (opp .zero (.even 0)) (opp .zero .zero)) .zero)
    (h .zero .zero (.even 0) .zero)

theorem target62095_not :
    ¬ ∀ x y : V,
      opp (opp x y) y = opp (opp (opp y x) y) y := by
  intro h
  exact (by decide :
    opp (opp (.odd 0) .zero) .zero ≠
      opp (opp (opp .zero (.odd 0)) .zero) .zero)
    (h (.odd 0) .zero)

theorem target20741_not :
    ¬ ∀ x y z : V,
      x = opp (opp y x) (opp (opp (opp y z) x) x) := by
  intro h
  exact (by decide :
    (.zero : V) ≠
      opp (opp .zero .zero)
        (opp (opp (opp .zero (.even 0)) .zero) .zero))
    (h .zero .zero (.even 0))

end DerivedParity


def DerivedParity.instMagma : Magma DerivedParity.V where
  op := DerivedParity.opp

def certificate : Goal := by
  refine ⟨DerivedParity.V, DerivedParity.instMagma, ?_, ?_⟩
  · intro x y z
    exact DerivedParity.source21105 x y z
  · exact DerivedParity.target51505_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21105_to_51505 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_21105_to_51505
