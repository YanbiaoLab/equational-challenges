-- Equation2531 → Equation1313
-- Recorded verdict: false
-- Premise: x = (y ◇ ((y ◇ x) ◇ x)) ◇ y
-- Conclusion: x = y ◇ (((y ◇ x) ◇ x) ◇ y)
-- Original submission SHA-256: b6d5e000e554f0b4f33dffe338980d989c354f78c7455f06e18e5838f57b746f
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ ((y ◇ x) ◇ x)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (((y ◇ x) ◇ x) ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Embedded module: JudgeDecide.DecideBang
section
/- decideFin! tactic: decides propositions over finite types by exhaustive checking. -/
           

macro "decideFin!" : tactic => `(tactic| decide)
end

-- Original submission body
                   
                             
                     

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace submission
abbrev C5 := Sum (Bool × Bool) (Unit)

def a0 : C5 := (.inl (false, false))
def a1 : C5 := (.inl (true, false))
def a2 : C5 := (.inl (false, true))
def a3 : C5 := (.inl (true, true))
def a4 : C5 := (.inr ())

def indexa : C5 → Nat
  | (.inl (false, false)) => 0
  | (.inl (true, false)) => 1
  | (.inl (false, true)) => 2
  | (.inl (true, true)) => 3
  | (.inr ()) => 4

abbrev C13 := Sum (Bool × Bool × Bool) (Sum (Bool × Bool) (Unit))

def b0 : C13 := (.inl (false, false, false))
def b1 : C13 := (.inl (true, false, false))
def b2 : C13 := (.inl (false, true, false))
def b3 : C13 := (.inl (true, true, false))
def b4 : C13 := (.inl (false, false, true))
def b5 : C13 := (.inl (true, false, true))
def b6 : C13 := (.inl (false, true, true))
def b7 : C13 := (.inl (true, true, true))
def b8 : C13 := (.inr (.inl (false, false)))
def b9 : C13 := (.inr (.inl (true, false)))
def b10 : C13 := (.inr (.inl (false, true)))
def b11 : C13 := (.inr (.inl (true, true)))
def b12 : C13 := (.inr (.inr ()))

def indexb : C13 → Nat
  | (.inl (false, false, false)) => 0
  | (.inl (true, false, false)) => 1
  | (.inl (false, true, false)) => 2
  | (.inl (true, true, false)) => 3
  | (.inl (false, false, true)) => 4
  | (.inl (true, false, true)) => 5
  | (.inl (false, true, true)) => 6
  | (.inl (true, true, true)) => 7
  | (.inr (.inl (false, false))) => 8
  | (.inr (.inl (true, false))) => 9
  | (.inr (.inl (false, true))) => 10
  | (.inr (.inl (true, true))) => 11
  | (.inr (.inr ())) => 12

def addRow0 : List C13 := [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12]
def addRow1 : List C13 := [b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b0]
def addRow2 : List C13 := [b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b0,b1]
def addRow3 : List C13 := [b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b0,b1,b2]
def addRow4 : List C13 := [b4,b5,b6,b7,b8,b9,b10,b11,b12,b0,b1,b2,b3]
def addRow5 : List C13 := [b5,b6,b7,b8,b9,b10,b11,b12,b0,b1,b2,b3,b4]
def addRow6 : List C13 := [b6,b7,b8,b9,b10,b11,b12,b0,b1,b2,b3,b4,b5]
def addRow7 : List C13 := [b7,b8,b9,b10,b11,b12,b0,b1,b2,b3,b4,b5,b6]
def addRow8 : List C13 := [b8,b9,b10,b11,b12,b0,b1,b2,b3,b4,b5,b6,b7]
def addRow9 : List C13 := [b9,b10,b11,b12,b0,b1,b2,b3,b4,b5,b6,b7,b8]
def addRow10 : List C13 := [b10,b11,b12,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9]
def addRow11 : List C13 := [b11,b12,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10]
def addRow12 : List C13 := [b12,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11]

def add13 (x y : C13) : C13 :=
  let row := match indexb x with
    | 0 => addRow0
    | 1 => addRow1
    | 2 => addRow2
    | 3 => addRow3
    | 4 => addRow4
    | 5 => addRow5
    | 6 => addRow6
    | 7 => addRow7
    | 8 => addRow8
    | 9 => addRow9
    | 10 => addRow10
    | 11 => addRow11
    | _ => addRow12
  row.getD (indexb y) b0

def scaleL : C13 → C13
  | (.inl (false, false, false)) => b0
  | (.inl (true, false, false)) => b9
  | (.inl (false, true, false)) => b5
  | (.inl (true, true, false)) => b1
  | (.inl (false, false, true)) => b10
  | (.inl (true, false, true)) => b6
  | (.inl (false, true, true)) => b2
  | (.inl (true, true, true)) => b11
  | (.inr (.inl (false, false))) => b7
  | (.inr (.inl (true, false))) => b3
  | (.inr (.inl (false, true))) => b12
  | (.inr (.inl (true, true))) => b8
  | (.inr (.inr ())) => b4

def scaleR : C13 → C13
  | (.inl (false, false, false)) => b0
  | (.inl (true, false, false)) => b5
  | (.inl (false, true, false)) => b10
  | (.inl (true, true, false)) => b2
  | (.inl (false, false, true)) => b7
  | (.inl (true, false, true)) => b12
  | (.inl (false, true, true)) => b4
  | (.inl (true, true, true)) => b9
  | (.inr (.inl (false, false))) => b1
  | (.inr (.inl (true, false))) => b6
  | (.inr (.inl (false, true))) => b11
  | (.inr (.inl (true, true))) => b3
  | (.inr (.inr ())) => b8

def outer : C5 → C5 → C5
  | (.inl (false, false)), (.inl (false, false)) => a0
  | (.inl (false, false)), (.inl (true, false)) => a4
  | (.inl (false, false)), (.inl (false, true)) => a3
  | (.inl (false, false)), (.inl (true, true)) => a2
  | (.inl (false, false)), (.inr ()) => a1
  | (.inl (true, false)), (.inl (false, false)) => a2
  | (.inl (true, false)), (.inl (true, false)) => a1
  | (.inl (true, false)), (.inl (false, true)) => a0
  | (.inl (true, false)), (.inl (true, true)) => a4
  | (.inl (true, false)), (.inr ()) => a3
  | (.inl (false, true)), (.inl (false, false)) => a4
  | (.inl (false, true)), (.inl (true, false)) => a3
  | (.inl (false, true)), (.inl (false, true)) => a2
  | (.inl (false, true)), (.inl (true, true)) => a1
  | (.inl (false, true)), (.inr ()) => a0
  | (.inl (true, true)), (.inl (false, false)) => a1
  | (.inl (true, true)), (.inl (true, false)) => a0
  | (.inl (true, true)), (.inl (false, true)) => a4
  | (.inl (true, true)), (.inl (true, true)) => a3
  | (.inl (true, true)), (.inr ()) => a2
  | (.inr ()), (.inl (false, false)) => a3
  | (.inr ()), (.inl (true, false)) => a2
  | (.inr ()), (.inl (false, true)) => a1
  | (.inr ()), (.inl (true, true)) => a0
  | (.inr ()), (.inr ()) => a4

def gamma : C5 → C5 → C13
  | (.inl (false, false)), (.inl (false, false)) => b0
  | (.inl (false, false)), (.inl (true, false)) => b1
  | (.inl (false, false)), (.inl (false, true)) => b0
  | (.inl (false, false)), (.inl (true, true)) => b0
  | (.inl (false, false)), (.inr ()) => b0
  | (.inl (true, false)), (.inl (false, false)) => b0
  | (.inl (true, false)), (.inl (true, false)) => b0
  | (.inl (true, false)), (.inl (false, true)) => b8
  | (.inl (true, false)), (.inl (true, true)) => b4
  | (.inl (true, false)), (.inr ()) => b10
  | (.inl (false, true)), (.inl (false, false)) => b5
  | (.inl (false, true)), (.inl (true, false)) => b7
  | (.inl (false, true)), (.inl (false, true)) => b0
  | (.inl (false, true)), (.inl (true, true)) => b3
  | (.inl (false, true)), (.inr ()) => b1
  | (.inl (true, true)), (.inl (false, false)) => b11
  | (.inl (true, true)), (.inl (true, false)) => b10
  | (.inl (true, true)), (.inl (false, true)) => b0
  | (.inl (true, true)), (.inl (true, true)) => b0
  | (.inl (true, true)), (.inr ()) => b4
  | (.inr ()), (.inl (false, false)) => b12
  | (.inr ()), (.inl (true, false)) => b0
  | (.inr ()), (.inl (false, true)) => b11
  | (.inr ()), (.inl (true, true)) => b4
  | (.inr ()), (.inr ()) => b0

abbrev CM := C5 × C13

def op (x y : CM) : CM :=
  (outer x.1 y.1, add13 (add13 (scaleL x.2) (scaleR y.2)) (gamma x.1 y.1))

end submission

def submission : Goal := by
  let m : Magma submission.CM := { op := submission.op }
  refine ⟨submission.CM, m, ?_⟩
  constructor
  · decideFin!
  · decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2531_to_1313 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2531_to_1313
