-- Equation20011 → Equation28879
-- Recorded verdict: true
-- Premise: x = (y * y) * ((y * (y * z)) * x)
-- Conclusion: x = (((y * z) * x) * x) * (x * x)
-- Original submission SHA-256: 6ece0056462a68619930a3565c3876e1e306a9c3222474a434308047a933dfea
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((y ◇ (y ◇ z)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ z) ◇ x) ◇ x) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ (((q1 ◇ q1) ◇ q0) ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => ((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (congrArg (fun t => t ◇ q2) (congrArg (fun t => (q1 ◇ q1) ◇ t) ((h q0 q1 q0).symm)))).symm).trans ((h q2 (q1 ◇ q1) ((q1 ◇ (q1 ◇ q0)) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), (((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ (q3 ◇ q5)) = q5:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => ((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ t) (congrArg (fun t => t ◇ q5) ((h q3 q4 q3).symm))).symm).trans (apc0 ((q4 ◇ (q4 ◇ q3)) ◇ q3) q4 q5)
  have apc2 : forall (q6 q7 q8:G), ((q6 ◇ q6) ◇ (q7 ◇ q8)) = q8:=by
    intro q6 q7 q8
    exact ((congrArg (fun t => t ◇ (q7 ◇ q8)) (apc1 (q6 ◇ q6) q6 (q6 ◇ q6))).symm).trans (apc1 q7 (q6 ◇ q6) q8)
  have apc3 : forall (q3 q4 q5 q6 q7 q8:G), (q4 ◇ (q3 ◇ q5)) = q5:=by
    intro q3 q4 q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ (q3 ◇ q5)) (apc2 q4 q4 q4)).symm).trans (apc1 q3 q4 q5)
  exact (apc3 x (((y ◇ z) ◇ x) ◇ x) x x x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20011_to_28879 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20011_to_28879
