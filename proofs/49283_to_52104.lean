-- Equation49283 → Equation52104
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * x) * (x * z)
-- Conclusion: x * x = ((x * (y * z)) * w) * u
-- Original submission SHA-256: df2c9a17565d5c0aa0eb10b8d1dc3e6c65565237433f6c429bbdeccef4409823
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ x) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = ((x ◇ (y ◇ z)) ◇ w) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y x x).trans ((h x x x x).symm)
  have apc1 : forall (x y z w:G), (((z ◇ w) ◇ x) ◇ (x ◇ x)) = (x ◇ x):=by
    intro x y z w
    exact (((apc0 x x (x ◇ x) (x ◇ x)).symm).trans ((h x x z w).trans (congrArg (fun t => ((z ◇ w) ◇ x) ◇ t) (apc0 x z (x ◇ z) (x ◇ z))))).symm
  have apc2 : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q2 ◇ q1)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((((apc1 q0 q0 q0 q0).symm).trans (h ((q0 ◇ q0) ◇ q0) (q0 ◇ q0) q2 q1)).trans (((congrArg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ q2)) (apc0 (q2 ◇ q1) ((q0 ◇ q0) ◇ q0) ((q2 ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)) ((q2 ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)))).trans (apc0 ((q2 ◇ q1) ◇ (q2 ◇ q1)) (((q0 ◇ q0) ◇ q0) ◇ q2) (((q2 ◇ q1) ◇ (q2 ◇ q1)) ◇ (((q0 ◇ q0) ◇ q0) ◇ q2)) (((q2 ◇ q1) ◇ (q2 ◇ q1)) ◇ (((q0 ◇ q0) ◇ q0) ◇ q2)))).trans (apc1 (q2 ◇ q1) (((q2 ◇ q1) ◇ (q2 ◇ q1)) ◇ ((q2 ◇ q1) ◇ (q2 ◇ q1))) q2 q1))).symm
  have apc4 : forall (q1 q3:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = ((q1 ◇ q1) ◇ q3):=by
    intro q1 q3
    exact ((apc0 (q1 ◇ q1) ((q1 ◇ q1) ◇ (q1 ◇ q1)) ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1)))).symm).trans (((congrArg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (apc1 q1 q1 q1 q1)).symm).trans ((h (q1 ◇ q1) q3 (q1 ◇ q1) q1).symm))
  have apc5 : forall (q1 q3:G), ((q1 ◇ q1) ◇ q3) = ((q1 ◇ q1) ◇ q1):=by
    intro q1 q3
    exact ((apc4 q1 q3).symm).trans (apc4 q1 q1)
  have apc9 : forall (q4 q5 q6 q7:G), ((q7 ◇ q5) ◇ q6) = ((q4 ◇ q4) ◇ q4):=by
    intro q4 q5 q6 q7
    exact ((((apc0 (q4 ◇ q4) ((q7 ◇ q5) ◇ q7) ((q4 ◇ q4) ◇ ((q7 ◇ q5) ◇ q7)) ((q4 ◇ q4) ◇ ((q7 ◇ q5) ◇ q7))).trans (apc5 q4 (q4 ◇ q4))).symm).trans (((congrArg (fun t => t ◇ ((q7 ◇ q5) ◇ q7)) (apc2 q4 q5 q7)).symm).trans ((h (q7 ◇ q5) q6 q7 q5).symm))).symm
  have apc10 : forall (q8 q9 q10 q11:G), ((q11 ◇ q9) ◇ q10) = (q8 ◇ q8):=by
    intro q8 q9 q10 q11
    exact (((apc1 q8 (((q8 ◇ q8) ◇ q8) ◇ (q8 ◇ q8)) q8 q8).symm).trans (((congrArg (fun t => t ◇ (q8 ◇ q8)) (apc5 q8 (q8 ◇ q8))).symm).trans ((apc9 (q8 ◇ q8) q9 q10 q11).symm))).symm
  have apc11 : forall (q12 q13 q14:G), (q14 ◇ q12) = (q13 ◇ q13):=by
    intro q12 q13 q14
    exact (h q14 q12 q12 q12).trans (apc10 q13 q14 (q14 ◇ q12) (q12 ◇ q12))
  exact (apc11 x (x ◇ x) x).trans ((apc11 u (x ◇ x) ((x ◇ (y ◇ z)) ◇ w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49283_to_52104 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49283_to_52104
