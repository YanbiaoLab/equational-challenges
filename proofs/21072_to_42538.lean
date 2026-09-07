-- Equation21072 → Equation42538
-- Recorded verdict: true
-- Premise: x = (y * z) * (((y * x) * z) * y)
-- Conclusion: x * x = y * (z * ((x * y) * z))
-- Original submission SHA-256: 6f9aed863a281380b0c921e4a2671c4d4ce951223eb8addb752d5d1f6c1705b3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (((y ◇ x) ◇ z) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (z ◇ ((x ◇ y) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ (((q2 ◇ q0) ◇ q1) ◇ q2)) ◇ (q0 ◇ q2)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ (((q2 ◇ q0) ◇ q1) ◇ q2)) ◇ t) (congrArg (fun t => t ◇ q2) ((h q0 q2 q1).symm))).symm).trans ((h q1 q2 (((q2 ◇ q0) ◇ q1) ◇ q2)).symm)
  have apc1 : forall (q3 q4 q5:G), ((q5 ◇ (q3 ◇ q5)) ◇ (q4 ◇ q5)) = (((q5 ◇ q3) ◇ q4) ◇ q5):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => (q5 ◇ (q3 ◇ q5)) ◇ t) (congrArg (fun t => t ◇ q5) (apc0 q3 q4 q5))).symm).trans ((h (((q5 ◇ q3) ◇ q4) ◇ q5) q5 (q3 ◇ q5)).symm)
  have apc2 : forall (q0 q1 q2 q3 q4 q5:G), (((q2 ◇ ((q2 ◇ q0) ◇ q1)) ◇ q0) ◇ q2) = q1:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((apc1 ((q2 ◇ q0) ◇ q1) q0 q2).symm).trans (apc0 q0 q1 q2)
  have apc3 : forall (q6 q7:G), ((q6 ◇ q6) ◇ (q7 ◇ q6)) = q7:=by
    intro q6 q7
    exact ((congrArg (fun t => t ◇ (q7 ◇ q6)) (congrArg (fun t => t ◇ q6) ((h q6 q7 q6).symm))).symm).trans (apc2 q6 q7 (q7 ◇ q6) q6 q6 q6)
  have apc5 : forall (x y z:G), ((y ◇ z) ◇ (((y ◇ x) ◇ z) ◇ y)) = ((x ◇ x) ◇ x):=by
    intro x y z
    exact (((h x y z).symm).trans (h x x x)).trans (apc3 x ((x ◇ x) ◇ x))
  have apc6 : forall (q8:G), ((q8 ◇ q8) ◇ q8) = q8:=by
    intro q8
    exact ((apc5 q8 q8 q8).symm).trans ((h q8 q8 q8).symm)
  have apc8 : forall (q9:G), (q9 ◇ q9) = q9:=by
    intro q9
    exact (((apc6 q9).symm).trans (((congrArg (fun t => (q9 ◇ q9) ◇ t) (apc6 q9)).symm).trans (apc3 q9 (q9 ◇ q9)))).symm
  have apc9 : forall (q6 q7 q9:G), (q6 ◇ (q7 ◇ q6)) = q7:=by
    intro q6 q7 q9
    exact ((congrArg (fun t => t ◇ (q7 ◇ q6)) (apc8 q6)).symm).trans (apc3 q6 q7)
  exact (calc
    (x ◇ x) = x:=apc8 x
    _ = (y ◇ (z ◇ ((x ◇ y) ◇ z))):=((congrArg (fun t => y ◇ t) (apc9 z (x ◇ y) (z ◇ ((x ◇ y) ◇ z)))).trans (apc9 y x (y ◇ (x ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21072_to_42538 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21072_to_42538
