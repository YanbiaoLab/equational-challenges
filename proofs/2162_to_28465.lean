-- Equation2162 → Equation28465
-- Recorded verdict: false
-- Premise: x = ((y ◇ z) ◇ x) ◇ (x ◇ y)
-- Conclusion: x = (((x ◇ y) ◇ y) ◇ x) ◇ (x ◇ z)
-- Original submission SHA-256: f87ffe6c574b3f15a4d7a893fb0ab7fb30a859af1796c3846090834cd92afc26
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ x) ◇ (x ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ y) ◇ x) ◇ (x ◇ z)
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
abbrev CM := Bool × Bool × Bool × Bool × Bool

def e0 : CM := (false, false, false, false, false)
def e1 : CM := (true, false, false, false, false)
def e2 : CM := (false, true, false, false, false)
def e3 : CM := (true, true, false, false, false)
def e4 : CM := (false, false, true, false, false)
def e5 : CM := (true, false, true, false, false)
def e6 : CM := (false, true, true, false, false)
def e7 : CM := (true, true, true, false, false)
def e8 : CM := (false, false, false, true, false)
def e9 : CM := (true, false, false, true, false)
def e10 : CM := (false, true, false, true, false)
def e11 : CM := (true, true, false, true, false)
def e12 : CM := (false, false, true, true, false)
def e13 : CM := (true, false, true, true, false)
def e14 : CM := (false, true, true, true, false)
def e15 : CM := (true, true, true, true, false)
def e16 : CM := (false, false, false, false, true)
def e17 : CM := (true, false, false, false, true)
def e18 : CM := (false, true, false, false, true)
def e19 : CM := (true, true, false, false, true)
def e20 : CM := (false, false, true, false, true)
def e21 : CM := (true, false, true, false, true)
def e22 : CM := (false, true, true, false, true)
def e23 : CM := (true, true, true, false, true)
def e24 : CM := (false, false, false, true, true)
def e25 : CM := (true, false, false, true, true)
def e26 : CM := (false, true, false, true, true)
def e27 : CM := (true, true, false, true, true)
def e28 : CM := (false, false, true, true, true)
def e29 : CM := (true, false, true, true, true)
def e30 : CM := (false, true, true, true, true)
def e31 : CM := (true, true, true, true, true)

def op (x y : CM) : CM :=
  (!x.2.2.2.2 && !y.2.2.2.1,
   !x.2.2.1 && !y.2.2.2.2,
   !x.2.2.2.1 && !y.2.1,
   !x.1 && !y.2.2.1,
   !x.2.1 && !y.1)

def separates : CM → Bool | (true, true, true, true, false) => true | _ => false
end submission

def submission : Goal := by
  let m : Magma submission.CM := { op := submission.op }
  refine ⟨submission.CM, m, ?_⟩
  constructor
  · rintro ⟨v0_0, v0_1, v0_2, v0_3, v0_4⟩ ⟨v1_0, v1_1, v1_2, v1_3, v1_4⟩ ⟨v2_0, v2_1, v2_2, v2_3, v2_4⟩
    apply Prod.ext
    · cases v0_0 <;> cases v1_2 <;> cases v2_4 <;> rfl
    · apply Prod.ext
      · cases v0_1 <;> cases v1_0 <;> cases v2_2 <;> rfl
      · apply Prod.ext
        · cases v0_2 <;> cases v1_4 <;> cases v2_3 <;> rfl
        · apply Prod.ext
          · cases v0_3 <;> cases v1_1 <;> cases v2_0 <;> rfl
          · cases v0_4 <;> cases v1_3 <;> cases v2_1 <;> rfl
  · intro h
    have bad := h submission.e15 submission.e0 submission.e15
    change submission.e15 = submission.op (submission.op (submission.op (submission.op (submission.e15) (submission.e0)) (submission.e0)) (submission.e15)) (submission.op (submission.e15) (submission.e15)) at bad
    have badBit := congrArg submission.separates bad
    change true = false at badBit
    exact Bool.noConfusion badBit

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2162_to_28465 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2162_to_28465
