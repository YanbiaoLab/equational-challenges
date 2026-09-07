-- Equation32289 → Equation21982
-- Recorded verdict: true
-- Premise: x = (y * ((y * (y * y)) * z)) * x
-- Conclusion: x = (y * (z * y)) * (z * (z * x))
-- Original submission SHA-256: 9f28c3bc4c3e3121b076c4d51b88c6af8e1ece7837c3dfac217625e1baafa089
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((y ◇ (y ◇ y)) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ y)) ◇ (z ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc2 : forall (q0 q1 q2 q3:G), ((((q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1)) ◇ ((q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1)) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1)))) ◇ q3) ◇ q2) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) ((h (((q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1)) ◇ ((q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1)) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1)))) ◇ q3) q0 q1).symm)).symm).trans ((h q2 (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1)) q3).symm)
  have apc3 : forall (q4 q5 q6 q7:G), ((((q4 ◇ ((q4 ◇ (q4 ◇ q4)) ◇ q5)) ◇ (q4 ◇ ((q4 ◇ (q4 ◇ q4)) ◇ q5))) ◇ q7) ◇ q6) = q6:=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ q6) (congrArg (fun t => t ◇ q7) ((h ((q4 ◇ ((q4 ◇ (q4 ◇ q4)) ◇ q5)) ◇ (q4 ◇ ((q4 ◇ (q4 ◇ q4)) ◇ q5))) q4 q5).symm))).symm).trans (apc2 q4 q5 q6 q7)
  have apc4 : forall (q8 q9 q10 q11:G), (((q8 ◇ ((q8 ◇ (q8 ◇ q8)) ◇ q9)) ◇ q11) ◇ q10) = q10:=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ q10) (congrArg (fun t => t ◇ q11) ((h (q8 ◇ ((q8 ◇ (q8 ◇ q8)) ◇ q9)) q8 q9).symm))).symm).trans (apc3 q8 q9 q10 q11)
  have apc5 : forall (q2 q3 q0 q1:G), (q3 ◇ q2) = q2:=by
    intro q2 q3 q0 q1
    exact ((congrArg (fun t => t ◇ q2) (apc4 q0 q1 q3 ((q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1)) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1))))).symm).trans (apc2 q0 q1 q2 q3)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (z ◇ y)) ◇ (z ◇ (z ◇ x))):=(((((congrArg (fun t => (y ◇ (z ◇ y)) ◇ t) (congrArg (fun t => z ◇ t) (apc5 x z (z ◇ x) (z ◇ x)))).trans (congrArg (fun t => t ◇ (z ◇ x)) (congrArg (fun t => y ◇ t) (apc5 y z (z ◇ y) (z ◇ y))))).trans (congrArg (fun t => t ◇ (z ◇ x)) (apc5 y y (y ◇ y) (y ◇ y)))).trans (congrArg (fun t => y ◇ t) (apc5 x z (z ◇ x) (z ◇ x)))).trans (apc5 x y (y ◇ x) (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32289_to_21982 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32289_to_21982
