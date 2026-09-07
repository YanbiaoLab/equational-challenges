-- Equation12658 → Equation36368
-- Recorded verdict: true
-- Premise: x = x * ((y * (x * (y * z))) * z)
-- Conclusion: x = (((x * y) * y) * (y * x)) * z
-- Original submission SHA-256: c38ca8b6609f2c292da39a0fc62921978fc2f487bca16256117d96b14b533481
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ (x ◇ (y ◇ z))) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ y) ◇ (y ◇ x)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ (((q0 ◇ (q1 ◇ (q0 ◇ q2))) ◇ q1) ◇ q2)) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => (q0 ◇ (q1 ◇ (q0 ◇ q2))) ◇ t) ((h q1 q0 q2).symm)))).symm).trans ((h q1 (q0 ◇ (q1 ◇ (q0 ◇ q2))) q2).symm)
  have apc4 : forall (q0 q3 q2:G), ((q0 ◇ (q3 ◇ (q0 ◇ (q3 ◇ q2)))) ◇ (q3 ◇ q2)) = (q0 ◇ (q3 ◇ (q0 ◇ (q3 ◇ q2)))):=by
    intro q0 q3 q2
    exact ((cg (fun t => (q0 ◇ (q3 ◇ (q0 ◇ (q3 ◇ q2)))) ◇ t) (cg (fun t => t ◇ q2) ((h q3 q0 (q3 ◇ q2)).symm))).symm).trans ((h (q0 ◇ (q3 ◇ (q0 ◇ (q3 ◇ q2)))) q3 q2).symm)
  have apc6 : forall (q4 q5 q6 q7:G), ((q4 ◇ (q5 ◇ (q4 ◇ q5))) ◇ q5) = (q4 ◇ (q5 ◇ (q4 ◇ q5))):=by
    intro q4 q5 q6 q7
    exact ((cg (fun t => (q4 ◇ (q5 ◇ (q4 ◇ q5))) ◇ t) (apc0 q6 q5 q7)).symm).trans ((((cg (fun t => t ◇ (q5 ◇ (((q6 ◇ (q5 ◇ (q6 ◇ q7))) ◇ q5) ◇ q7))) (cg (fun t => q4 ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => q4 ◇ t) (apc0 q6 q5 q7))))).symm).trans (apc4 q4 q5 (((q6 ◇ (q5 ◇ (q6 ◇ q7))) ◇ q5) ◇ q7))).trans (cg (fun t => q4 ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => q4 ◇ t) (apc0 q6 q5 q7)))))
  have apc7 : forall (q8 q9:G), (q9 ◇ (q8 ◇ (q9 ◇ (q8 ◇ q9)))) = q9:=by
    intro q8 q9
    exact ((cg (fun t => q9 ◇ t) (apc6 q8 q9 q8 q8)).symm).trans ((h q9 q8 q9).symm)
  have apc8 : forall (q10 q11:G), (q11 ◇ (q10 ◇ q11)) = q11:=by
    intro q10 q11
    exact (((cg (fun t => t ◇ (q10 ◇ q11)) (apc7 q10 q11)).symm).trans (apc4 q11 q10 q11)).trans (apc7 q10 q11)
  have apc9 : forall (q12 q13 q14:G), (q12 ◇ q13) = q12:=by
    intro q12 q13 q14
    exact (((cg (fun t => q12 ◇ t) (cg (fun t => t ◇ (q14 ◇ q13)) (apc8 q12 q13))).trans (cg (fun t => q12 ◇ t) (apc8 q14 q13))).symm).trans (((cg (fun t => q12 ◇ t) (cg (fun t => t ◇ (q14 ◇ q13)) (cg (fun t => q13 ◇ t) (cg (fun t => q12 ◇ t) (apc8 q14 q13))))).symm).trans ((h q12 q13 (q14 ◇ q13)).symm))
  exact (calc
    x = x:=rfl
    _ = ((((x ◇ y) ◇ y) ◇ (y ◇ x)) ◇ z):=(((((cg (fun t => t ◇ z) (cg (fun t => t ◇ (y ◇ x)) (cg (fun t => t ◇ y) (apc9 x y (x ◇ y))))).trans (cg (fun t => t ◇ z) (cg (fun t => t ◇ (y ◇ x)) (apc9 x y (x ◇ y))))).trans (cg (fun t => t ◇ z) (cg (fun t => x ◇ t) (apc9 y x (y ◇ x))))).trans (cg (fun t => t ◇ z) (apc9 x y (x ◇ y)))).trans (apc9 x z (x ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_12658_to_36368 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_12658_to_36368
