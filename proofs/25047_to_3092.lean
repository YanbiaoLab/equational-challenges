-- Equation25047 → Equation3092
-- Recorded verdict: true
-- Premise: x = (x * (y * (z * w))) * (x * u)
-- Conclusion: x = (((x * y) * z) * y) * w
-- Original submission SHA-256: 5a0735969c892e03ef89d9e8cc557fa0a6b8920bc789442621aff243b13405ab
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ (y ◇ (z ◇ w))) ◇ (x ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((x ◇ y) ◇ z) ◇ y) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q1 ◇ q0)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q1 ◇ q0)) (congrArg (fun t => q1 ◇ t) ((h q2 q0 q0 q0 q0).symm))).symm).trans ((h q1 (q2 ◇ (q0 ◇ (q0 ◇ q0))) q2 q0 q0).symm)
  have apc1 : forall (q3 q4 q5:G), (((q3 ◇ q4) ◇ q5) ◇ q3) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => ((q3 ◇ q4) ◇ q5) ◇ t) (apc0 q3 q3 q4)).symm).trans (apc0 (q3 ◇ q3) (q3 ◇ q4) q5)
  have apc2 : forall (q6 q7 q8:G), ((q8 ◇ q6) ◇ q7) = q8:=by
    intro q6 q7 q8
    exact (((apc0 q6 q8 q6).symm).trans (((congrArg (fun t => t ◇ (q8 ◇ q6)) (apc1 q8 q6 q7)).symm).trans (apc1 (q8 ◇ q6) q7 q8))).symm
  exact ((apc2 y z x).symm).trans ((apc2 y w ((x ◇ y) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25047_to_3092 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25047_to_3092
