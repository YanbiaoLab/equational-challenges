-- Equation45239 → Equation46826
-- Recorded verdict: false
-- Premise: x ◇ x = y ◇ (((z ◇ w) ◇ u) ◇ v)
-- Conclusion: x ◇ x = (x ◇ y) ◇ ((z ◇ x) ◇ x)
-- Original submission SHA-256: f51b7251636b4479c15612bf8c6dc1d69d4c24e0f76b69e8c4868156e65ed079
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ x = y ◇ (((z ◇ w) ◇ u) ◇ v)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (x ◇ y) ◇ ((z ◇ x) ◇ x)
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
abbrev CM := Sum (Bool × Bool × Bool) (Bool × Bool)

def e0 : CM := (.inl (false, false, false))
def e1 : CM := (.inl (true, false, false))
def e2 : CM := (.inl (false, true, false))
def e3 : CM := (.inl (true, true, false))
def e4 : CM := (.inl (false, false, true))
def e5 : CM := (.inl (true, false, true))
def e6 : CM := (.inl (false, true, true))
def e7 : CM := (.inl (true, true, true))
def e8 : CM := (.inr (false, false))
def e9 : CM := (.inr (true, false))
def e10 : CM := (.inr (false, true))
def e11 : CM := (.inr (true, true))

def r0 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e10
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e10
  | (.inl (true, false, true)) => e10
  | (.inl (false, true, true)) => e10
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e10
  | (.inr (true, true)) => e8

def r1 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e8
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e10
  | (.inl (true, true, true)) => e10
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e8

def r2 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e11
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e11
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e9

def r3 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e10
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e11
  | (.inl (false, true, true)) => e11
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e8

def r4 : CM → CM
  | (.inl (false, false, false)) => e10
  | (.inl (true, false, false)) => e10
  | (.inl (false, true, false)) => e10
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e8

def r5 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e8
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e9
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e9

def r6 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e8
  | (.inl (false, true, false)) => e11
  | (.inl (true, true, false)) => e11
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e8

def r7 : CM → CM
  | (.inl (false, false, false)) => e9
  | (.inl (true, false, false)) => e10
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e9
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e10
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e10
  | (.inr (true, true)) => e8

def r8 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e8
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e8

def r9 : CM → CM
  | (.inl (false, false, false)) => e9
  | (.inl (true, false, false)) => e8
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e9
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e9

def r10 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e8
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e8
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e8
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e8
  | (.inr (true, true)) => e8

def r11 : CM → CM
  | (.inl (false, false, false)) => e8
  | (.inl (true, false, false)) => e8
  | (.inl (false, true, false)) => e8
  | (.inl (true, true, false)) => e10
  | (.inl (false, false, true)) => e8
  | (.inl (true, false, true)) => e8
  | (.inl (false, true, true)) => e10
  | (.inl (true, true, true)) => e8
  | (.inr (false, false)) => e8
  | (.inr (true, false)) => e8
  | (.inr (false, true)) => e10
  | (.inr (true, true)) => e8

def op : CM → CM → CM
  | (.inl (false, false, false)), y => r0 y
  | (.inl (true, false, false)), y => r1 y
  | (.inl (false, true, false)), y => r2 y
  | (.inl (true, true, false)), y => r3 y
  | (.inl (false, false, true)), y => r4 y
  | (.inl (true, false, true)), y => r5 y
  | (.inl (false, true, true)), y => r6 y
  | (.inl (true, true, true)), y => r7 y
  | (.inr (false, false)), y => r8 y
  | (.inr (true, false)), y => r9 y
  | (.inr (false, true)), y => r10 y
  | (.inr (true, true)), y => r11 y

def staticIndex : CM → Nat
  | (.inl (false, false, false)) => 0
  | (.inl (true, false, false)) => 1
  | (.inl (false, true, false)) => 2
  | (.inl (true, true, false)) => 3
  | (.inl (false, false, true)) => 4
  | (.inl (true, false, true)) => 5
  | (.inl (false, true, true)) => 6
  | (.inl (true, true, true)) => 7
  | (.inr (false, false)) => 8
  | (.inr (true, false)) => 9
  | (.inr (false, true)) => 10
  | (.inr (true, true)) => 11

def staticRange0 (qStatic : CM) : Bool :=
  Nat.testBit 3840 (staticIndex qStatic)

theorem staticRangeStep0 : ∀ staticA staticB : CM,
    staticRange0 (op staticA staticB) = true := by
  decideFin!

def staticRange1 (qStatic : CM) : Bool :=
  Nat.testBit 1792 (staticIndex qStatic)

theorem staticRangeStep1 : ∀ staticA staticB : CM,
    staticRange0 staticA = true →
    staticRange1 (op staticA staticB) = true := by
  decideFin!

def staticRange2 (qStatic : CM) : Bool :=
  Nat.testBit 768 (staticIndex qStatic)

theorem staticRangeStep2 : ∀ staticA staticB : CM,
    staticRange1 staticA = true →
    staticRange2 (op staticA staticB) = true := by
  decideFin!

theorem staticSourceRelational : ∀ x y qStatic : CM,
    staticRange2 qStatic = true →
    op (x) (x) = op (y) (qStatic) := by
  decideFin!

def separates : CM → Bool | (.inr (false, false)) => true | _ => false
end submission

def submission : Goal := by
  let m : Magma submission.CM := { op := submission.op }
  refine ⟨submission.CM, m, ?_⟩
  constructor
  · intro x y z w u v
    change submission.op (x) (x) = submission.op (y) (submission.op (submission.op (submission.op (z) (w)) (u)) (v))
    exact submission.staticSourceRelational x y (submission.op (submission.op (submission.op (z) (w)) (u)) (v)) (submission.staticRangeStep2 (submission.op (submission.op (z) (w)) (u)) (v) (submission.staticRangeStep1 (submission.op (z) (w)) (u) (submission.staticRangeStep0 (z) (w))))
  · intro h
    have bad := h submission.e3 submission.e5 submission.e6
    have badBit := congrArg submission.separates bad
    change true = false at badBit
    exact Bool.noConfusion badBit

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45239_to_46826 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_45239_to_46826
