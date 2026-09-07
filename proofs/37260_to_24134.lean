-- Equation37260 → Equation24134
-- Recorded verdict: true
-- Premise: x = ((x * (y * (y * z))) * y) * w
-- Conclusion: x = ((x * y) * z) * ((y * x) * z)
-- Original submission SHA-256: 1a8304e265988c84b2140fb832799b3971c2b339e71280efe42b53d037748f31
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ (y ◇ (y ◇ z))) ◇ y) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ z) ◇ ((y ◇ x) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q4 ◇ q0) ◇ ((q0 ◇ (q1 ◇ (q1 ◇ q2))) ◇ q1)) ◇ q3) = q4:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ ((q0 ◇ (q1 ◇ (q1 ◇ q2))) ◇ q1)) (congrArg (fun t => q4 ◇ t) ((h q0 q1 q2 (((q0 ◇ (q1 ◇ (q1 ◇ q2))) ◇ q1) ◇ q0)).symm)))).symm).trans ((h q4 ((q0 ◇ (q1 ◇ (q1 ◇ q2))) ◇ q1) q0 q3).symm)
  have apc1 : forall (q5 q6 q7:G), (q6 ◇ q7) = (q6 ◇ q5):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ q7) (apc0 q5 q5 q5 ((((q5 ◇ (q5 ◇ (q5 ◇ q5))) ◇ q5) ◇ (q5 ◇ (q5 ◇ q5))) ◇ q5) q6)).symm).trans (apc0 ((q5 ◇ (q5 ◇ (q5 ◇ q5))) ◇ q5) q5 q5 q7 (q6 ◇ q5))
  have apc2 : forall (q8 q9 q10 q11:G), (((q10 ◇ q8) ◇ q11) ◇ q9) = q10:=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ q9) (congrArg (fun t => t ◇ q11) (apc1 q8 q10 (q11 ◇ (q11 ◇ q8))))).symm).trans ((h q10 q11 q8 q9).symm)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ y) ◇ z) ◇ ((y ◇ x) ◇ z)):=(apc2 y ((y ◇ x) ◇ z) x z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_37260_to_24134 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_37260_to_24134
