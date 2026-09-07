-- Equation34759 → Equation35056
-- Recorded verdict: true
-- Premise: x = ((y * x) * ((y * x) * z)) * x
-- Conclusion: x = ((y * z) * ((x * z) * y)) * x
-- Original submission SHA-256: bd1686a805fa023106ec0455a6b4a647bdbc22dcca7d4370b68bcce8cca8734b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ ((y ◇ x) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ ((x ◇ z) ◇ y)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (((y ◇ x) ◇ ((y ◇ x) ◇ z)) ◇ x) = (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) = q0:=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc2 : forall (q1 q2:G), ((q1 ◇ (q1 ◇ q2)) ◇ q1) = q1:=by
    intro q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q2) (apc1 q1)))).symm).trans (((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ ((((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q1) ◇ q2)) (apc1 q1))).symm).trans ((h q1 ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) q2).symm))
  have apc3 : forall (q3 q4:G), (q4 ◇ (q4 ◇ q3)) = (q4 ◇ q3):=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ (q4 ◇ q3)) (apc2 q4 q3)).symm).trans (((congrArg (fun t => t ◇ (q4 ◇ q3)) (congrArg (fun t => (q4 ◇ (q4 ◇ q3)) ◇ t) (apc2 q4 q3))).symm).trans ((h (q4 ◇ q3) q4 q4).symm))
  have apc4 : forall (q5 q6 q7:G), (((q6 ◇ q5) ◇ q7) ◇ q5) = q5:=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ q5) (apc3 q7 (q6 ◇ q5))).symm).trans ((h q5 q6 q7).symm)
  have apc7 : forall (q8 q9 q10:G), (q9 ◇ q8) = q8:=by
    intro q8 q9 q10
    exact ((congrArg (fun t => t ◇ q8) (apc4 q9 q10 q8)).symm).trans (((congrArg (fun t => t ◇ q8) (congrArg (fun t => ((q10 ◇ q9) ◇ q8) ◇ t) (apc4 q9 q10 q8))).symm).trans ((h q8 (q10 ◇ q9) q9).symm))
  exact (apc7 x ((y ◇ z) ◇ ((x ◇ z) ◇ y)) x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34759_to_35056 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_34759_to_35056
