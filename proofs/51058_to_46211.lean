-- Equation51058 → Equation46211
-- Recorded verdict: true
-- Premise: x * y = (z * ((w * x) * u)) * w
-- Conclusion: x * y = (x * z) * (y * (x * w))
-- Original submission SHA-256: 33838f9803820648723ce311347f2f47d364f14c2ae7e974e7f827307caa7808
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ ((w ◇ x) ◇ u)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ z) ◇ (y ◇ (x ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc1 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc2 : forall (q0 q1 q2 q3 q4:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact (((((cg (fun t => t ◇ (q1 ◇ ((q2 ◇ q0) ◇ q3))) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q3) (apc1 q2 q0 (q2 ◇ q0) (q2 ◇ q0) (q2 ◇ q0))))).trans (cg (fun t => (q1 ◇ ((q2 ◇ q2) ◇ q3)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q3) (apc1 q2 q0 (q2 ◇ q0) (q2 ◇ q0) (q2 ◇ q0)))))).trans (cg (fun t => t ◇ (q1 ◇ ((q2 ◇ q2) ◇ q3))) (apc1 q1 ((q2 ◇ q2) ◇ q3) (q1 ◇ ((q2 ◇ q2) ◇ q3)) (q1 ◇ ((q2 ◇ q2) ◇ q3)) (q1 ◇ ((q2 ◇ q2) ◇ q3))))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (apc1 q1 ((q2 ◇ q2) ◇ q3) (q1 ◇ ((q2 ◇ q2) ◇ q3)) (q1 ◇ ((q2 ◇ q2) ◇ q3)) (q1 ◇ ((q2 ◇ q2) ◇ q3))))).symm).trans ((((apc1 (q1 ◇ ((q2 ◇ q0) ◇ q3)) q2 q3 q3 q3).symm).trans ((h q0 q4 q1 q2 q3).symm)).trans (apc1 q0 q4 (q0 ◇ q4) (q0 ◇ q4) (q0 ◇ q4)))
  have apc5 : forall (x y z w u:G), ((z ◇ z) ◇ w) = ((x ◇ x) ◇ x):=by
    intro x y z w u
    exact (((cg (fun t => t ◇ w) (cg (fun t => z ◇ t) (cg (fun t => t ◇ u) (apc1 w x (w ◇ x) (w ◇ x) (w ◇ x))))).trans (cg (fun t => t ◇ w) (apc1 z ((w ◇ w) ◇ u) (z ◇ ((w ◇ w) ◇ u)) (z ◇ ((w ◇ w) ◇ u)) (z ◇ ((w ◇ w) ◇ u))))).symm).trans ((((h x y z w u).symm).trans (h x y x x x)).trans (cg (fun t => t ◇ x) (apc1 x ((x ◇ x) ◇ x) (x ◇ ((x ◇ x) ◇ x)) (x ◇ ((x ◇ x) ◇ x)) (x ◇ ((x ◇ x) ◇ x)))))
  have apc6 : forall (q5 q6 q7 q8 q9 q10:G), ((q6 ◇ q6) ◇ (q5 ◇ q5)) = (q5 ◇ q5):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((cg (fun t => t ◇ (q5 ◇ q5)) (apc1 q6 (((q7 ◇ q7) ◇ q8) ◇ q9) (q6 ◇ (((q7 ◇ q7) ◇ q8) ◇ q9)) (q6 ◇ (((q7 ◇ q7) ◇ q8) ◇ q9)) (q6 ◇ (((q7 ◇ q7) ◇ q8) ◇ q9)))).symm).trans ((((cg (fun t => t ◇ (q5 ◇ q5)) (cg (fun t => q6 ◇ t) (cg (fun t => t ◇ q9) ((apc5 q5 q8 q7 q8 q8).symm)))).symm).trans ((h q5 q10 q6 (q5 ◇ q5) q9).symm)).trans (apc1 q5 q10 (q5 ◇ q10) (q5 ◇ q10) (q5 ◇ q10)))
  have apc7 : forall (q11 q12 q13 q14:G), ((q12 ◇ q12) ◇ q11) = (q11 ◇ q11):=by
    intro q11 q12 q13 q14
    exact ((cg (fun t => t ◇ q11) (apc1 q12 (q13 ◇ q13) (q12 ◇ (q13 ◇ q13)) (q12 ◇ (q13 ◇ q13)) (q12 ◇ (q13 ◇ q13)))).symm).trans ((((cg (fun t => t ◇ q11) (cg (fun t => q12 ◇ t) (apc2 q13 q11 q13 q13 q13))).symm).trans ((h q11 q14 q12 q11 (q11 ◇ q11)).symm)).trans (apc1 q11 q14 (q11 ◇ q14) (q11 ◇ q14) (q11 ◇ q14)))
  have apc8 : forall (q13 q11 q14 q12 q8 q7 q9 q5 q10 q6:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q5 ◇ q5):=by
    intro q13 q11 q14 q12 q8 q7 q9 q5 q10 q6
    exact ((apc7 (q5 ◇ q5) q6 ((q6 ◇ q6) ◇ (q5 ◇ q5)) ((q6 ◇ q6) ◇ (q5 ◇ q5))).symm).trans (apc6 q5 q6 q7 q8 q9 q10)
  exact (calc
    (x ◇ y) = (x ◇ x):=apc1 x y (x ◇ y) (x ◇ y) (x ◇ y)
    _ = ((x ◇ z) ◇ (y ◇ (x ◇ w))):=((((cg (fun t => t ◇ (y ◇ (x ◇ w))) (apc1 x z (x ◇ z) (x ◇ z) (x ◇ z))).trans (cg (fun t => (x ◇ x) ◇ t) (apc1 y (x ◇ w) (y ◇ (x ◇ w)) (y ◇ (x ◇ w)) (y ◇ (x ◇ w))))).trans (apc1 (x ◇ x) (y ◇ y) ((x ◇ x) ◇ (y ◇ y)) ((x ◇ x) ◇ (y ◇ y)) ((x ◇ x) ◇ (y ◇ y)))).trans (apc8 ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) x ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51058_to_46211 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51058_to_46211
