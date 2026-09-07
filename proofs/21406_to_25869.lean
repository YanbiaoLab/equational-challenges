-- Equation21406 → Equation25869
-- Recorded verdict: true
-- Premise: x = (x * (x * y)) * (z * (w * y))
-- Conclusion: x = (x * ((y * z) * x)) * (x * x)
-- Original submission SHA-256: 868ca3db951d27c75273640d53a385540919cadc6a2223c81e9330fa04bf1a7a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (x ◇ y)) ◇ (z ◇ (w ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ z) ◇ x)) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ (q3 ◇ (q0 ◇ q2))) ◇ q1) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ (q3 ◇ (q0 ◇ q2))) ◇ t) ((h q1 q2 q0 q0).symm)).symm).trans ((h q3 (q0 ◇ q2) (q1 ◇ (q1 ◇ q2)) q0).symm)
  have apc2 : forall (q4 q5 q6:G), ((q5 ◇ (q5 ◇ q6)) ◇ q4) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => (q5 ◇ (q5 ◇ q6)) ◇ t) (apc0 q4 (q4 ◇ q6) q4 q4)).symm).trans ((h q5 q6 (q4 ◇ (q4 ◇ (q4 ◇ q4))) q4).symm)
  have apc3 : forall (q7 q8 q9:G), (q7 ◇ (q7 ◇ q9)) = (q7 ◇ q8):=by
    intro q7 q8 q9
    exact (((congrArg (fun t => t ◇ q8) ((h q7 q9 (q7 ◇ (q7 ◇ q9)) q7).symm)).symm).trans (apc0 q7 q8 q9 (q7 ◇ (q7 ◇ q9)))).symm
  have apc4 : forall (q10 q11 q12:G), ((q12 ◇ q10) ◇ q11) = q12:=by
    intro q10 q11 q12
    exact ((congrArg (fun t => t ◇ q11) (apc3 q12 q10 q10)).symm).trans (apc2 q11 q12 q10)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ ((y ◇ z) ◇ x)) ◇ (x ◇ x)):=((congrArg (fun t => t ◇ (x ◇ x)) (congrArg (fun t => x ◇ t) (apc4 z x y))).trans (apc4 y (x ◇ x) x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21406_to_25869 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21406_to_25869
