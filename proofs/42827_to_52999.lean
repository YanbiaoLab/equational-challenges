-- Equation42827 → Equation52999
-- Recorded verdict: true
-- Premise: x * y = y * (y * ((z * z) * z))
-- Conclusion: x * x = (((y * x) * y) * z) * y
-- Original submission SHA-256: 4e6f2fc6e12670eed162de9a63687382cd92a602c9dc930c6b887ab35a2a7387
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ ((z ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (((y ◇ x) ◇ y) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0).trans ((h q1 q2 q0).symm)).symm
  have apc2 : forall (q3 q4 q5:G), (q4 ◇ (q4 ◇ (q5 ◇ q5))) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => q4 ◇ t) ((apc0 (q5 ◇ q5) q5 q3).symm))).symm).trans ((h q3 q4 q5).symm)
  have apc3 : forall (q6 q7:G), (q7 ◇ (q7 ◇ (q6 ◇ q6))) = (q7 ◇ q7):=by
    intro q6 q7
    exact (apc2 q6 q7 q6).trans ((apc0 q6 q7 q6).symm)
  have apc4 : forall (q8 q9 q10 q11:G), (q10 ◇ (q10 ◇ (q8 ◇ q11))) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => q10 ◇ t) (congrArg (fun t => q10 ◇ t) (apc1 q8 (q11 ◇ q11) q11))).symm).trans ((h q9 q10 q11).symm)
  have apc6 : forall (q12 q13 q14:G), (q13 ◇ (q12 ◇ q13)) = (q14 ◇ q13):=by
    intro q12 q13 q14
    exact ((congrArg (fun t => q13 ◇ t) (apc4 q12 q12 q13 q12)).symm).trans (apc4 q13 q14 q13 (q12 ◇ q12))
  have apc7 : forall (q15 q16 q17:G), ((q15 ◇ q17) ◇ (q15 ◇ q17)) = (q16 ◇ q17):=by
    intro q15 q16 q17
    exact (((apc6 q15 q17 q16).symm).trans ((apc0 q17 (q15 ◇ q17) q15).symm)).symm
  have apc8 : forall (q18 q19:G), ((q18 ◇ q19) ◇ (q18 ◇ q19)) = (q19 ◇ q19):=by
    intro q18 q19
    exact (apc7 q18 q18 q19).trans ((apc0 q18 q19 q18).symm)
  have apc9 : forall (q20 q21:G), (q21 ◇ q21) = (q20 ◇ q20):=by
    intro q20 q21
    exact (((congrArg (fun t => (q21 ◇ q21) ◇ t) (apc3 q20 q21)).trans (apc8 q21 q21)).symm).trans ((((congrArg (fun t => t ◇ (q21 ◇ (q21 ◇ (q20 ◇ q20)))) (apc3 q20 q21)).symm).trans (apc8 q21 (q21 ◇ (q20 ◇ q20)))).trans ((apc8 q21 (q20 ◇ q20)).trans (apc8 q20 q20)))
  have apc10 : forall (q22 q23 q24:G), (q23 ◇ q24) = (q22 ◇ q22):=by
    intro q22 q23 q24
    exact (((apc9 q22 q24).symm).trans (apc0 q23 q24 q22)).symm
  exact (apc10 (x ◇ x) x x).trans ((apc10 (x ◇ x) (((y ◇ x) ◇ y) ◇ z) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42827_to_52999 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42827_to_52999
