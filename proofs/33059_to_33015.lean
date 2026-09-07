-- Equation33059 → Equation33015
-- Recorded verdict: true
-- Premise: x = (y ◇ (((x ◇ z) ◇ y) ◇ y)) ◇ z
-- Conclusion: x = (y ◇ (((x ◇ y) ◇ y) ◇ z)) ◇ x
-- Original submission SHA-256: 1c465f90fe1c95968cb0093402bff6c0c7e60f6180ecd9c6c7ed26600fa98b7f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (((x ◇ z) ◇ y) ◇ y)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (((x ◇ y) ◇ y) ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), ((y ◇ (((x ◇ z) ◇ y) ◇ y)) ◇ z) = ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (q0 q1 q2:G), ((q2 ◇ (q0 ◇ q2)) ◇ (((q0 ◇ q2) ◇ q1) ◇ q1)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (((q0 ◇ q2) ◇ q1) ◇ q1)) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q2) ((h q0 q1 q2).symm)))).symm).trans ((h q1 q2 (((q0 ◇ q2) ◇ q1) ◇ q1)).symm)
  have apc3 : forall (q3 q4:G), ((q4 ◇ (q3 ◇ q4)) ◇ q4) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q4) (apc2 q3 (q4 ◇ (q3 ◇ q4)) q4)).symm).trans ((h q3 (q4 ◇ (q3 ◇ q4)) q4).symm)
  have apc4 : forall (q5 q6:G), ((q5 ◇ q6) ◇ q6) = q5:=by
    intro q5 q6
    exact ((apc3 ((q5 ◇ q6) ◇ q6) q6).symm).trans ((h q5 q6 q6).symm)
  have apc6 : forall (q7 q8 q9:G), ((q8 ◇ (q7 ◇ q9)) ◇ q9) = q7:=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ q9) (congrArg (fun t => q8 ◇ t) (apc4 (q7 ◇ q9) q8))).symm).trans ((h q7 q8 q9).symm)
  have apc11 : forall (q10 q11 q12:G), q11 = q10:=by
    intro q10 q11 q12
    exact (((((congrArg (fun t => t ◇ (((q12 ◇ q11) ◇ q10) ◇ q10)) (congrArg (fun t => q11 ◇ t) (congrArg (fun t => t ◇ q11) (congrArg (fun t => t ◇ q12) (congrArg (fun t => q12 ◇ t) (congrArg (fun t => t ◇ q12) (apc4 q12 q12))))))).trans (congrArg (fun t => t ◇ (((q12 ◇ q11) ◇ q10) ◇ q10)) (congrArg (fun t => q11 ◇ t) (congrArg (fun t => t ◇ q11) (apc6 q12 q12 q12))))).trans (congrArg (fun t => (q11 ◇ (q12 ◇ q11)) ◇ t) (apc4 (q12 ◇ q11) q10))).trans (apc4 q11 (q12 ◇ q11))).symm).trans (((congrArg (fun t => t ◇ (((q12 ◇ q11) ◇ q10) ◇ q10)) (congrArg (fun t => q11 ◇ t) (congrArg (fun t => t ◇ q11) (apc0 q12 q10 q11)))).symm).trans ((h q10 q11 (((q12 ◇ q11) ◇ q10) ◇ q10)).symm))
  exact (apc11 x x x).trans ((apc11 x ((y ◇ (((x ◇ y) ◇ y) ◇ z)) ◇ x) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_33059_to_33015 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_33059_to_33015
