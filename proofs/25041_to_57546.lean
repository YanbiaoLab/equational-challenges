-- Equation25041 → Equation57546
-- Recorded verdict: true
-- Premise: x = (x * (y * (z * z))) * (w * w)
-- Conclusion: x * (y * x) = ((x * z) * z) * x
-- Original submission SHA-256: 95271988d1b0147b4e2c10db837377c2ed4287c5fbe2fa035f59bd118bd4ee20
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (y ◇ (z ◇ z))) ◇ (w ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = ((x ◇ z) ◇ z) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q1 ◇ q1)) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q1 ◇ q1)) (congrArg (fun t => q2 ◇ t) ((h q0 q0 q0 q0).symm))).symm).trans ((h q2 (q0 ◇ (q0 ◇ (q0 ◇ q0))) q0 q1).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ (q5 ◇ q5)) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ (q5 ◇ q5)) (apc0 q3 q3 q4)).symm).trans (apc0 (q3 ◇ q3) q5 (q4 ◇ q3))
  have apc2 : forall (q3 q4 q5:G), (q4 ◇ q4) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact (((apc1 q3 q4 q5).symm).trans (apc1 q4 q4 q5)).symm
  have apc3 : forall (q6 q7:G), (q6 ◇ (q7 ◇ q7)) = (q6 ◇ q6):=by
    intro q6 q7
    exact ((apc2 q6 q6 q6).trans ((apc1 q6 q6 q7).symm)).symm
  have apc4 : forall (q8 q9 q10:G), (q9 ◇ (q10 ◇ q8)) = (q9 ◇ q9):=by
    intro q8 q9 q10
    exact ((congrArg (fun t => q9 ◇ t) (apc2 q8 q10 q8)).symm).trans (apc3 q9 q10)
  have apc5 : forall (q3 q11 q12:G), ((q12 ◇ q11) ◇ q3) = q12:=by
    intro q3 q11 q12
    exact ((congrArg (fun t => (q12 ◇ q11) ◇ t) (apc0 q3 q3 q3)).symm).trans (apc0 q11 (q3 ◇ q3) q12)
  exact (calc
    (x ◇ (y ◇ x)) = (x ◇ x):=apc4 x x y
    _ = (((x ◇ z) ◇ z) ◇ x):=(congrArg (fun t => t ◇ x) (apc5 z z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25041_to_57546 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25041_to_57546
