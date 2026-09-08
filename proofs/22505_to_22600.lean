-- Equation22505 → Equation22600
-- Recorded verdict: false
-- Premise: x = (y ◇ (x ◇ y)) ◇ ((z ◇ z) ◇ z)
-- Conclusion: x = (y ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ y)
-- Original submission SHA-256: 1cef3338011f3e0def2d5fd7db6bc736777131ff6998ae3026882f66f5a78293
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ y)) ◇ ((z ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ y)
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
abbrev CM := Sum (Bool × Bool × Bool) (Sum (Bool) (Unit))

def e0 : CM := (.inl (false, false, false))
def e1 : CM := (.inl (true, false, false))
def e2 : CM := (.inl (false, true, false))
def e3 : CM := (.inl (true, true, false))
def e4 : CM := (.inl (false, false, true))
def e5 : CM := (.inl (true, false, true))
def e6 : CM := (.inl (false, true, true))
def e7 : CM := (.inl (true, true, true))
def e8 : CM := (.inr (.inl false))
def e9 : CM := (.inr (.inl true))
def e10 : CM := (.inr (.inr ()))

def r0 : CM → CM
  | (.inl (false, false, false)) => e10
  | (.inl (true, false, false)) => e3
  | (.inl (false, true, false)) => e5
  | (.inl (true, true, false)) => e0
  | (.inl (false, false, true)) => e9
  | (.inl (true, false, true)) => e2
  | (.inl (false, true, true)) => e6
  | (.inl (true, true, true)) => e1
  | (.inr (.inl false)) => e4
  | (.inr (.inl true)) => e7
  | (.inr (.inr ())) => e8

def r1 : CM → CM
  | (.inl (false, false, false)) => e3
  | (.inl (true, false, false)) => e4
  | (.inl (false, true, false)) => e6
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e0
  | (.inl (true, false, true)) => e1
  | (.inl (false, true, true)) => e2
  | (.inl (true, true, true)) => e10
  | (.inr (.inl false)) => e7
  | (.inr (.inl true)) => e9
  | (.inr (.inr ())) => e5

def r2 : CM → CM
  | (.inl (false, false, false)) => e2
  | (.inl (true, false, false)) => e10
  | (.inl (false, true, false)) => e9
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e4
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e0
  | (.inl (true, true, true)) => e6
  | (.inr (.inl false)) => e3
  | (.inr (.inl true)) => e5
  | (.inr (.inr ())) => e1

def r3 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e1
  | (.inl (false, true, false)) => e4
  | (.inl (true, true, false)) => e2
  | (.inl (false, false, true)) => e6
  | (.inl (true, false, true)) => e9
  | (.inl (false, true, true)) => e10
  | (.inl (true, true, true)) => e5
  | (.inr (.inl false)) => e0
  | (.inr (.inl true)) => e3
  | (.inr (.inr ())) => e7

def r4 : CM → CM
  | (.inl (false, false, false)) => e0
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e1
  | (.inl (true, true, false)) => e6
  | (.inl (false, false, true)) => e5
  | (.inl (true, false, true)) => e10
  | (.inl (false, true, true)) => e4
  | (.inl (true, true, true)) => e3
  | (.inr (.inl false)) => e9
  | (.inr (.inl true)) => e8
  | (.inr (.inr ())) => e2

def r5 : CM → CM
  | (.inl (false, false, false)) => e1
  | (.inl (true, false, false)) => e0
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e9
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e6
  | (.inl (false, true, true)) => e3
  | (.inl (true, true, true)) => e2
  | (.inr (.inl false)) => e5
  | (.inr (.inl true)) => e4
  | (.inr (.inr ())) => e10

def r6 : CM → CM
  | (.inl (false, false, false)) => e5
  | (.inl (true, false, false)) => e6
  | (.inl (false, true, false)) => e0
  | (.inl (true, true, false)) => e3
  | (.inl (false, false, true)) => e10
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e9
  | (.inr (.inl false)) => e2
  | (.inr (.inl true)) => e1
  | (.inr (.inr ())) => e4

def r7 : CM → CM
  | (.inl (false, false, false)) => e9
  | (.inl (true, false, false)) => e8
  | (.inl (false, true, false)) => e3
  | (.inl (true, true, false)) => e10
  | (.inl (false, false, true)) => e1
  | (.inl (true, false, true)) => e4
  | (.inl (false, true, true)) => e5
  | (.inl (true, true, true)) => e7
  | (.inr (.inl false)) => e6
  | (.inr (.inl true)) => e2
  | (.inr (.inr ())) => e0

def r8 : CM → CM
  | (.inl (false, false, false)) => e4
  | (.inl (true, false, false)) => e9
  | (.inl (false, true, false)) => e2
  | (.inl (true, true, false)) => e5
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e3
  | (.inl (false, true, true)) => e7
  | (.inl (true, true, true)) => e0
  | (.inr (.inl false)) => e1
  | (.inr (.inl true)) => e10
  | (.inr (.inr ())) => e6

def r9 : CM → CM
  | (.inl (false, false, false)) => e6
  | (.inl (true, false, false)) => e2
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e4
  | (.inl (false, false, true)) => e3
  | (.inl (true, false, true)) => e5
  | (.inl (false, true, true)) => e1
  | (.inl (true, true, true)) => e8
  | (.inr (.inl false)) => e10
  | (.inr (.inl true)) => e0
  | (.inr (.inr ())) => e9

def r10 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e5
  | (.inl (false, true, false)) => e10
  | (.inl (true, true, false)) => e1
  | (.inl (false, false, true)) => e2
  | (.inl (true, false, true)) => e0
  | (.inl (false, true, true)) => e9
  | (.inl (true, true, true)) => e4
  | (.inr (.inl false)) => e8
  | (.inr (.inl true)) => e6
  | (.inr (.inr ())) => e3

def op : CM → CM → CM
  | (.inl (false, false, false)), y => r0 y
  | (.inl (true, false, false)), y => r1 y
  | (.inl (false, true, false)), y => r2 y
  | (.inl (true, true, false)), y => r3 y
  | (.inl (false, false, true)), y => r4 y
  | (.inl (true, false, true)), y => r5 y
  | (.inl (false, true, true)), y => r6 y
  | (.inl (true, true, true)), y => r7 y
  | (.inr (.inl false)), y => r8 y
  | (.inr (.inl true)), y => r9 y
  | (.inr (.inr ())), y => r10 y

theorem staticSourceConst0 : ∀ z : CM, op (op (z) (z)) (z) = e7 := by
  decideFin!

theorem staticSourceResidual : ∀ x y : CM, x = op (op (y) (op (x) (y))) (e7) := by
  decideFin!

def separates : CM → Bool | (.inl (false, false, false)) => true | _ => false
end submission

def submission : Goal := by
  let m : Magma submission.CM := { op := submission.op }
  refine ⟨submission.CM, m, ?_⟩
  constructor
  · intro x y z
    change x = submission.op (submission.op (y) (submission.op (x) (y))) (submission.op (submission.op (z) (z)) (z))
    rw [submission.staticSourceConst0 z] <;> exact submission.staticSourceResidual x y
  · intro h
    have bad := h submission.e0 submission.e1
    have badBit := congrArg submission.separates bad
    change true = false at badBit
    exact Bool.noConfusion badBit

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22505_to_22600 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_22505_to_22600
