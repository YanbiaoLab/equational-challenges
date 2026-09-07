-- Equation6993 → Equation39775
-- Recorded verdict: true
-- Premise: x = y * (z * ((x * z) * (y * y)))
-- Conclusion: x = (((x * (x * x)) * x) * x) * x
-- Original submission SHA-256: a67e85fc9f1d86b667b81f587b8c587105ef3d455a8f57f9634a5a6db1046e2e
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((x ◇ z) ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q1 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q2))) ◇ (q0 ◇ (q3 ◇ q3)))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => (q1 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q2))) ◇ t) (cg (fun t => t ◇ (q3 ◇ q3)) ((h q0 q2 q1).symm)))).symm).trans ((h q2 q3 (q1 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q2)))).symm)
  have apc1 : forall (q4:G), ((q4 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) ◇ (q4 ◇ q4)) = q4:=by
    intro q4
    exact ((cg (fun t => (q4 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) ◇ t) (cg (fun t => q4 ◇ t) (apc0 q4 q4 q4 (q4 ◇ q4)))).symm).trans ((h q4 (q4 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) q4).symm)
  have apc2 : forall (q5:G), (q5 ◇ (q5 ◇ q5)) = (q5 ◇ q5):=by
    intro q5
    exact ((cg (fun t => q5 ◇ t) (apc1 (q5 ◇ q5))).symm).trans (apc0 (q5 ◇ q5) (q5 ◇ q5) (q5 ◇ q5) q5)
  have apc3 : forall (q6 q7:G), ((q6 ◇ q7) ◇ (q7 ◇ ((q6 ◇ q7) ◇ (q6 ◇ q7)))) = q6:=by
    intro q6 q7
    exact ((cg (fun t => (q6 ◇ q7) ◇ t) (cg (fun t => q7 ◇ t) (apc2 (q6 ◇ q7)))).symm).trans ((h q6 (q6 ◇ q7) q7).symm)
  have apc4 : forall (q8:G), ((q8 ◇ q8) ◇ (q8 ◇ q8)) = q8:=by
    intro q8
    exact (((((cg (fun t => (q8 ◇ q8) ◇ t) (cg (fun t => (q8 ◇ q8) ◇ t) (cg (fun t => t ◇ (q8 ◇ (q8 ◇ q8))) (apc2 q8)))).trans (cg (fun t => (q8 ◇ q8) ◇ t) (cg (fun t => (q8 ◇ q8) ◇ t) (cg (fun t => (q8 ◇ q8) ◇ t) (apc2 q8))))).trans (cg (fun t => (q8 ◇ q8) ◇ t) (apc2 (q8 ◇ q8)))).trans (apc2 (q8 ◇ q8))).symm).trans (((cg (fun t => t ◇ ((q8 ◇ q8) ◇ ((q8 ◇ (q8 ◇ q8)) ◇ (q8 ◇ (q8 ◇ q8))))) (apc2 q8)).symm).trans (apc3 q8 (q8 ◇ q8)))
  have apc7 : forall (q9:G), (q9 ◇ q9) = q9:=by
    intro q9
    exact ((apc2 q9).symm).trans (((cg (fun t => q9 ◇ t) (cg (fun t => q9 ◇ t) (apc4 q9))).symm).trans ((h q9 q9 q9).symm))
  exact (calc
    x = x:=rfl
    _ = ((((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ x):=(((((cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (cg (fun t => x ◇ t) (apc7 x))))).trans (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc7 x))))).trans (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc7 x)))).trans (cg (fun t => t ◇ x) (apc7 x))).trans (apc7 x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6993_to_39775 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6993_to_39775
