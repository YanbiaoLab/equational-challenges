-- Equation5934 → Equation43667
-- Recorded verdict: true
-- Premise: x = y ◇ (y ◇ (x ◇ ((x ◇ z) ◇ z)))
-- Conclusion: x ◇ y = y ◇ ((x ◇ z) ◇ (z ◇ z))
-- Original submission SHA-256: ef540140fb3f61528b997d6f992bce956c3dd2d1b0d9d3d7bd904e2a6b3ccd64
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (x ◇ ((x ◇ z) ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ ((x ◇ z) ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (y ◇ (y ◇ (x ◇ ((x ◇ z) ◇ z)))) = (x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (q0:G), (q0 ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))) = q0:=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc2 : forall (q1 q2:G), (q2 ◇ (q2 ◇ (q1 ◇ q1))) = q1:=by
    intro q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (apc1 q1)))).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ ((q1 ◇ q1) ◇ q1)))) (apc1 q1))))).symm).trans ((h q1 q2 (q1 ◇ (q1 ◇ ((q1 ◇ q1) ◇ q1)))).symm))
  have apc3 : forall (q3:G), ((q3 ◇ q3) ◇ q3) = (q3 ◇ q3):=by
    intro q3
    exact ((cg (fun t => (q3 ◇ q3) ◇ t) (apc2 q3 (q3 ◇ q3))).symm).trans (apc2 (q3 ◇ q3) (q3 ◇ q3))
  have apc5 : forall (q0 q3:G), (q0 ◇ q0) = q0:=by
    intro q0 q3
    exact ((cg (fun t => q0 ◇ t) (apc2 q0 q0)).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (apc3 q0)))).symm).trans (apc1 q0))
  have apc6 : forall (q4 q5:G), (q4 ◇ ((q4 ◇ q5) ◇ q5)) = q4:=by
    intro q4 q5
    exact ((apc5 (q4 ◇ ((q4 ◇ q5) ◇ q5)) ((q4 ◇ ((q4 ◇ q5) ◇ q5)) ◇ (q4 ◇ ((q4 ◇ q5) ◇ q5)))).symm).trans (((cg (fun t => (q4 ◇ ((q4 ◇ q5) ◇ q5)) ◇ t) (apc5 (q4 ◇ ((q4 ◇ q5) ◇ q5)) q4)).symm).trans ((h q4 (q4 ◇ ((q4 ◇ q5) ◇ q5)) q5).symm))
  have apc7 : forall (q6 q7 q8:G), (q7 ◇ (q6 ◇ (q7 ◇ q6))) = q7:=by
    intro q6 q7 q8
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => q7 ◇ t) (apc6 q6 q8)))).symm).trans (((cg (fun t => q7 ◇ t) (cg (fun t => t ◇ (q7 ◇ (q6 ◇ ((q6 ◇ q8) ◇ q8)))) ((h q6 q7 q8).symm))).symm).trans (apc6 q7 (q7 ◇ (q6 ◇ ((q6 ◇ q8) ◇ q8)))))
  have apc8 : forall (q0 q1 q2 q3:G), (q2 ◇ (q2 ◇ q1)) = q1:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (apc5 q1 (q1 ◇ q1)))).symm).trans (apc2 q1 q2)
  have apc9 : forall (q9 q10:G), (q9 ◇ (q10 ◇ q9)) = q10:=by
    intro q9 q10
    exact (((apc5 q10 (q10 ◇ q10)).symm).trans (((cg (fun t => q10 ◇ t) (apc7 q9 q10 q9)).symm).trans (apc8 q9 (q9 ◇ (q10 ◇ q9)) q10 q9))).symm
  have apc10 : forall (q11 q12:G), (q12 ◇ q11) = (q11 ◇ q12):=by
    intro q11 q12
    exact ((cg (fun t => q12 ◇ t) (apc9 q12 q11)).symm).trans (apc8 q11 (q11 ◇ q12) q12 q11)
  have apc12 : forall (q0 q1 q2 q3:G), ((q1 ◇ q2) ◇ q2) = q1:=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => q2 ◇ t) (apc10 q1 q2)).trans (apc10 (q1 ◇ q2) q2)).symm).trans (((apc8 q0 q1 q2 q3).trans ((apc8 q0 q1 q1 q3).symm)).trans ((cg (fun t => q1 ◇ t) (apc5 q1 (q1 ◇ q1))).trans (apc5 q1 (q1 ◇ q1))))
  exact (calc
    (x ◇ y) = (x ◇ y):=rfl
    _ = (y ◇ ((x ◇ z) ◇ (z ◇ z))):=(((cg (fun t => y ◇ t) (cg (fun t => (x ◇ z) ◇ t) (apc5 z (z ◇ z)))).trans (cg (fun t => y ◇ t) (apc12 ((x ◇ z) ◇ z) x z ((x ◇ z) ◇ z)))).trans (apc10 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5934_to_43667 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5934_to_43667
