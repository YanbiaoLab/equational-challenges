-- Equation4208 → Equation48202
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * x) * x
-- Conclusion: x * y = (z * (x * y)) * (w * x)
-- Original submission SHA-256: 87317e6f891113050aeacbd3d456cee22dba67bfd12796de3c15318d20dc7cf9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ y) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ y)) ◇ (w ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) ((h q1 q0 q0).symm)).symm).trans ((h q1 q1 (q0 ◇ q0)).symm)
  have apc1 : forall (q2 q3:G), ((q3 ◇ q2) ◇ (q3 ◇ q2)) = ((q3 ◇ q2) ◇ q2):=by
    intro q2 q3
    exact ((apc0 (q3 ◇ q2) (q3 ◇ q2)).symm).trans ((h (q3 ◇ q2) q2 q3).symm)
  have apc2 : forall (q4 q2:G), (q4 ◇ q2) = (q4 ◇ q4):=by
    intro q4 q2
    exact (((apc0 q4 q4).symm).trans (((congrArg (fun t => t ◇ q4) (apc0 q2 q4)).symm).trans ((h q4 q2 q4).symm))).symm
  have apc3 : forall (q5 q6:G), ((q6 ◇ q5) ◇ q5) = (q6 ◇ q6):=by
    intro q5 q6
    exact ((apc1 q5 q6).symm).trans (((apc2 (q6 ◇ q5) q6).symm).trans (apc0 q5 q6))
  have apc4 : forall (q7 q8 q9:G), ((q8 ◇ q7) ◇ (q8 ◇ q7)) = (q9 ◇ q7):=by
    intro q7 q8 q9
    exact ((h q9 q7 q8).trans (apc3 q9 (q8 ◇ q7))).symm
  have apc5 : forall (x y z:G), ((z ◇ y) ◇ (z ◇ y)) = (x ◇ x):=by
    intro x y z
    exact ((apc3 x (z ◇ y)).symm).trans ((((h x y z).symm).trans (h x y x)).trans (((congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (apc2 x y))).trans (congrArg (fun t => t ◇ x) (apc0 x x))).trans (apc0 x x)))
  have apc10 : forall (q10 q11 q12 q13:G), ((q11 ◇ q10) ◇ (q11 ◇ q10)) = (q13 ◇ q12):=by
    intro q10 q11 q12 q13
    exact (apc5 (q10 ◇ q12) q10 q11).trans (apc4 q12 q10 q13)
  exact ((apc10 (x ◇ y) ((z ◇ (x ◇ y)) ◇ (w ◇ x)) y x).symm).trans (apc10 (x ◇ y) ((z ◇ (x ◇ y)) ◇ (w ◇ x)) (w ◇ x) (z ◇ (x ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4208_to_48202 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4208_to_48202
