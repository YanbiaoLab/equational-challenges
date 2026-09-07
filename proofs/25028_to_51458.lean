-- Equation25028 → Equation51458
-- Recorded verdict: true
-- Premise: x = (x * (y * (z * z))) * (x * z)
-- Conclusion: x * y = ((x * z) * (x * y)) * y
-- Original submission SHA-256: 1840d67cb16bacfa49ad284af89215cf22f2437b3045aceb50718d8507e34d21
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ (z ◇ z))) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((x ◇ z) ◇ (x ◇ y)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q1)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ (q0 ◇ q1)) (congrArg (fun t => q0 ◇ t) ((h q1 q0 q1).symm))).symm).trans ((h q0 (q1 ◇ (q0 ◇ (q1 ◇ q1))) q1).symm)
  have apc3 : forall (q2 q3:G), (q2 ◇ q3) = (q2 ◇ q2):=by
    intro q2 q3
    exact (((congrArg (fun t => q2 ◇ t) (apc0 q2 q3)).symm).trans (((congrArg (fun t => t ◇ ((q2 ◇ q3) ◇ (q2 ◇ q3))) (apc0 q2 q3)).symm).trans (apc0 (q2 ◇ q3) (q2 ◇ q3)))).symm
  have apc9 : forall (q4 q5 q6 q7:G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = q4:=by
    intro q4 q5 q6 q7
    exact ((((congrArg (fun t => (q4 ◇ (q5 ◇ q6)) ◇ t) (congrArg (fun t => q4 ◇ t) (apc3 q6 q7))).trans (congrArg (fun t => (q4 ◇ (q5 ◇ q6)) ◇ t) (apc3 q4 (q6 ◇ q6)))).trans (congrArg (fun t => t ◇ (q4 ◇ q4)) (apc3 q4 (q5 ◇ q6)))).symm).trans (((congrArg (fun t => t ◇ (q4 ◇ (q6 ◇ q7))) (congrArg (fun t => q4 ◇ t) (congrArg (fun t => q5 ◇ t) (apc0 q6 q7)))).symm).trans ((h q4 q5 (q6 ◇ q7)).symm))
  exact (calc
    (x ◇ y) = (x ◇ x):=apc3 x y
    _ = (((x ◇ z) ◇ (x ◇ y)) ◇ y):=((((congrArg (fun t => t ◇ y) (congrArg (fun t => (x ◇ z) ◇ t) (apc3 x y))).trans (congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ (x ◇ x)) (apc3 x z)))).trans (congrArg (fun t => t ◇ y) (apc9 x ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x))))).trans (apc3 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25028_to_51458 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25028_to_51458
