-- Equation40721 → Equation43542
-- Recorded verdict: true
-- Premise: x = ((((x * y) * x) * y) * z) * y
-- Conclusion: x * y = x * ((y * y) * (z * w))
-- Original submission SHA-256: 44166db177c64582dd70b1cea7578eb5a9a8fcb921d0148b4aa2be19291a9999
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((((x ◇ y) ◇ x) ◇ y) ◇ z) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ ((y ◇ y) ◇ (z ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q2) ◇ q1) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q2) ((h q0 q1 ((q0 ◇ q1) ◇ q0)).symm))).symm).trans ((h ((q0 ◇ q1) ◇ q0) q1 q2).symm)
  have apc1 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ q1) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1 q2
    exact ((((apc0 q0 q1 q2).trans (apc0 q0 q0 q1)).symm).trans ((apc0 q0 q1 q2).trans ((apc0 q0 q1 q0).symm))).symm
  have apc4 : forall (q3 q4 q5:G), (((((q3 ◇ q3) ◇ q3) ◇ q4) ◇ q5) ◇ q4) = q3:=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ q4) (cg (fun t => t ◇ q5) (cg (fun t => t ◇ q4) (apc0 q3 q3 q4)))).symm).trans ((h q3 q4 q5).symm)
  have apc7 : forall (q6 q7 q8 q9:G), (((q6 ◇ q7) ◇ q8) ◇ (q6 ◇ q7)) = (((q6 ◇ q6) ◇ q6) ◇ q8):=by
    intro q6 q7 q8 q9
    exact (((cg (fun t => t ◇ q8) (apc0 q6 q6 q9)).symm).trans (((cg (fun t => t ◇ q8) (apc0 q6 q9 q7)).symm).trans (apc0 (q6 ◇ q7) q8 q9))).symm
  have apc8 : forall (q0 q10 q1 q2:G), ((((q0 ◇ q0) ◇ q0) ◇ q2) ◇ q1) = ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q10):=by
    intro q0 q10 q1 q2
    exact ((((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q1) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q10) (cg (fun t => t ◇ q1) (apc0 q0 q0 q1))))))).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q2) (apc0 q0 q1 ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q10))))).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q2) (apc0 q0 q0 q1)))).symm).trans ((((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((((q0 ◇ q1) ◇ q0) ◇ q1) ◇ q10)) ((h q0 q1 q10).symm))))).symm).trans ((h ((((q0 ◇ q1) ◇ q0) ◇ q1) ◇ q10) q1 q2).symm)).trans (cg (fun t => t ◇ q10) (cg (fun t => t ◇ q1) (apc0 q0 q0 q1))))
  have apc9 : forall (q11 q12 q13:G), ((((((q11 ◇ q11) ◇ q11) ◇ q11) ◇ q11) ◇ q13) ◇ ((q11 ◇ q11) ◇ q11)) = (q11 ◇ q12):=by
    intro q11 q12 q13
    exact ((((cg (fun t => t ◇ q12) (apc4 q11 ((q11 ◇ q11) ◇ q11) ((q11 ◇ q11) ◇ q11))).symm).trans ((apc8 ((q11 ◇ q11) ◇ q11) q12 ((q11 ◇ q11) ◇ q11) q13).symm)).trans ((((((cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (cg (fun t => t ◇ q13) (apc7 (q11 ◇ q11) q11 ((q11 ◇ q11) ◇ q11) ((((q11 ◇ q11) ◇ q11) ◇ ((q11 ◇ q11) ◇ q11)) ◇ ((q11 ◇ q11) ◇ q11))))).trans (cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (cg (fun t => t ◇ q13) (cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (cg (fun t => t ◇ (q11 ◇ q11)) (apc1 q11 (q11 ◇ q11) ((q11 ◇ q11) ◇ (q11 ◇ q11)))))))).trans (cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (cg (fun t => t ◇ q13) (cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (apc7 q11 q11 q11 (((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q11))))))).trans (cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (cg (fun t => t ◇ q13) (apc7 (q11 ◇ q11) q11 q11 ((((q11 ◇ q11) ◇ q11) ◇ q11) ◇ ((q11 ◇ q11) ◇ q11)))))).trans (cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (cg (fun t => t ◇ q13) (cg (fun t => t ◇ q11) (cg (fun t => t ◇ (q11 ◇ q11)) (apc1 q11 (q11 ◇ q11) ((q11 ◇ q11) ◇ (q11 ◇ q11)))))))).trans (cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (cg (fun t => t ◇ q13) (cg (fun t => t ◇ q11) (apc7 q11 q11 q11 (((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q11)))))))).symm
  exact ((apc9 x y (x ◇ y)).symm).trans (apc9 x ((y ◇ y) ◇ (z ◇ w)) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_40721_to_43542 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_40721_to_43542
