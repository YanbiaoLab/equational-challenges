-- Equation32990 → Equation52516
-- Recorded verdict: true
-- Premise: x = (y ◇ (((x ◇ x) ◇ z) ◇ z)) ◇ x
-- Conclusion: x ◇ y = ((y ◇ (z ◇ z)) ◇ x) ◇ y
-- Original submission SHA-256: e749a1a2af1aadaed57d959db1638fe96e2d0c1f08c504724a1948cabfc8e859
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (((x ◇ x) ◇ z) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ (z ◇ z)) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q1) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) ((h (((q0 ◇ q0) ◇ q1) ◇ q1) q0 q0).symm)).symm).trans ((h q0 (q0 ◇ ((((((q0 ◇ q0) ◇ q1) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) ◇ q0) ◇ q0)) q1).symm)
  have apc2 : forall (q2 q3 q1:G), ((q3 ◇ (q1 ◇ q1)) ◇ (((q1 ◇ q1) ◇ q2) ◇ q2)) = (((q1 ◇ q1) ◇ q2) ◇ q2):=by
    intro q2 q3 q1
    exact ((congrArg (fun t => t ◇ (((q1 ◇ q1) ◇ q2) ◇ q2)) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q1) ((h q1 (((q1 ◇ q1) ◇ q2) ◇ q2) q2).symm)))).symm).trans ((h (((q1 ◇ q1) ◇ q2) ◇ q2) q3 q1).symm)
  have apc6 : forall (q4 q5:G), (((((q5 ◇ q5) ◇ q4) ◇ q4) ◇ (((q5 ◇ q5) ◇ q4) ◇ q4)) ◇ (q5 ◇ q5)) = (q5 ◇ q5):=by
    intro q4 q5
    exact ((congrArg (fun t => t ◇ (q5 ◇ q5)) (congrArg (fun t => t ◇ (((q5 ◇ q5) ◇ q4) ◇ q4)) (apc2 q4 (q5 ◇ q5) q5))).symm).trans (apc0 (q5 ◇ q5) (((q5 ◇ q5) ◇ q4) ◇ q4))
  have apc7 : forall (q6:G), ((((q6 ◇ q6) ◇ (q6 ◇ q6)) ◇ (q6 ◇ q6)) ◇ (q6 ◇ q6)) = (q6 ◇ q6):=by
    intro q6
    exact ((congrArg (fun t => t ◇ (q6 ◇ q6)) (apc2 (q6 ◇ q6) ((q6 ◇ q6) ◇ (q6 ◇ q6)) q6)).symm).trans (apc6 (q6 ◇ q6) q6)
  have apc14 : forall (q7 q8:G), ((q8 ◇ (q7 ◇ q7)) ◇ (q7 ◇ q7)) = (q7 ◇ q7):=by
    intro q7 q8
    exact ((congrArg (fun t => t ◇ (q7 ◇ q7)) (congrArg (fun t => q8 ◇ t) (apc7 q7))).symm).trans ((h (q7 ◇ q7) q8 (q7 ◇ q7)).symm)
  have apc17 : forall (q9 q10 q11:G), ((q11 ◇ (q9 ◇ q9)) ◇ q10) = q10:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ q10) (congrArg (fun t => q11 ◇ t) (apc14 q9 (q10 ◇ q10)))).symm).trans ((h q10 q11 (q9 ◇ q9)).symm)
  exact (calc
    (x ◇ y) = (x ◇ y):=rfl
    _ = (((y ◇ (z ◇ z)) ◇ x) ◇ y):=(congrArg (fun t => t ◇ y) (apc17 z x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32990_to_52516 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32990_to_52516
