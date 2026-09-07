-- Equation23351 → Equation41739
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ x) ◇ (z ◇ (w ◇ u))
-- Conclusion: x ◇ y = x ◇ (x ◇ (x ◇ (z ◇ y)))
-- Original submission SHA-256: d4db5595a616573955019a9dc11a73952c4346e7f011078a8879441a0afc6ed2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ x) ◇ x) ◇ (z ◇ (w ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (x ◇ (x ◇ (z ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q1) ◇ q1) ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => ((q2 ◇ q1) ◇ q1) ◇ t) ((h q0 q0 q0 q0 q0).symm)).symm).trans ((h q1 q2 ((q0 ◇ q0) ◇ q0) q0 (q0 ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q5 ◇ (q6 ◇ (q4 ◇ q3))) = q5:=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ (q6 ◇ (q4 ◇ q3))) (apc0 q5 q5 q3)).symm).trans ((h q5 (q3 ◇ q5) q6 q4 q3).symm)
  have apc2 : forall (q7 q8 q9 q10 q11:G), (q9 ◇ (q8 ◇ q7)) = (q11 ◇ q10):=by
    intro q7 q8 q9 q10 q11
    exact (((congrArg (fun t => t ◇ q10) (apc1 q7 q8 q11 q9)).symm).trans (((congrArg (fun t => t ◇ q10) (apc1 q7 q8 (q11 ◇ (q9 ◇ (q8 ◇ q7))) q9)).symm).trans (apc0 q10 (q9 ◇ (q8 ◇ q7)) q11))).symm
  have apc3 : forall (q7 q8 q9 q10 q11:G), (q11 ◇ q10) = (q7 ◇ q7):=by
    intro q7 q8 q9 q10 q11
    exact ((apc2 q7 q8 q9 q10 q11).symm).trans (apc2 q7 q8 q9 q7 q7)
  exact (apc3 (x ◇ y) (x ◇ y) (x ◇ y) y x).trans ((apc3 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ (x ◇ (z ◇ y))) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23351_to_41739 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23351_to_41739
