-- Equation54886 → Equation53813
-- Recorded verdict: false
-- Premise: x ◇ (x ◇ y) = z ◇ ((w ◇ u) ◇ v)
-- Conclusion: x ◇ (x ◇ x) = x ◇ (y ◇ (x ◇ y))
-- Original submission SHA-256: f5fff1608b1ec3763b364fca30a1393e21e28b5704f5ecfa959a8d1a11020412
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (x ◇ y) = z ◇ ((w ◇ u) ◇ v)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = x ◇ (y ◇ (x ◇ y))
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
abbrev CM := Sum (Bool × Bool × Bool) (Unit)

def e0 : CM := (.inl (false, false, false))
def e1 : CM := (.inl (true, false, false))
def e2 : CM := (.inl (false, true, false))
def e3 : CM := (.inl (true, true, false))
def e4 : CM := (.inl (false, false, true))
def e5 : CM := (.inl (true, false, true))
def e6 : CM := (.inl (false, true, true))
def e7 : CM := (.inl (true, true, true))
def e8 : CM := (.inr ())

def r0 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e6
  | (.inl (false, true, true)) => e7
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e6

def r1 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e7
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e7

def r2 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e7

def r3 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e6
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e7
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e6

def r4 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e7
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e7

def r5 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e7

def r6 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e7
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e7

def r7 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e7
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e7

def r8 : CM → CM
  | (.inl (false, false, false)) => e7
  | (.inl (true, false, false)) => e7
  | (.inl (false, true, false)) => e7
  | (.inl (true, true, false)) => e7
  | (.inl (false, false, true)) => e7
  | (.inl (true, false, true)) => e7
  | (.inl (false, true, true)) => e7
  | (.inl (true, true, true)) => e7
  | (.inr ()) => e7

def op : CM → CM → CM
  | (.inl (false, false, false)), y => r0 y
  | (.inl (true, false, false)), y => r1 y
  | (.inl (false, true, false)), y => r2 y
  | (.inl (true, true, false)), y => r3 y
  | (.inl (false, false, true)), y => r4 y
  | (.inl (true, false, true)), y => r5 y
  | (.inl (false, true, true)), y => r6 y
  | (.inl (true, true, true)), y => r7 y
  | (.inr ()), y => r8 y

theorem staticSourceLeft : ∀ x y : CM, op (x) (op (x) (y)) = e7 := by
  decideFin!

theorem staticSourceRight : ∀ z w u v : CM, op (z) (op (op (w) (u)) (v)) = e7 := by
  intro z
  fin_cases z <;> decideFin!

def separates : CM → Bool | (.inl (true, true, true)) => true | _ => false
end submission

def submission : Goal := by
  let m : Magma submission.CM := { op := submission.op }
  refine ⟨submission.CM, m, ?_⟩
  constructor
  · intro x y z w u v
    change submission.op (x) (submission.op (x) (y)) = submission.op (z) (submission.op (submission.op (w) (u)) (v))
    exact (submission.staticSourceLeft x y).trans (submission.staticSourceRight z w u v).symm
  · intro h
    have bad := h submission.e0 submission.e5
    have badBit := congrArg submission.separates bad
    change true = false at badBit
    exact Bool.noConfusion badBit

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54886_to_53813 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_54886_to_53813
