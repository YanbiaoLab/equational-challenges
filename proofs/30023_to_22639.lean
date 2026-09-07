-- Equation30023 → Equation22639
-- Recorded verdict: true
-- Premise: x = (y * (z * (w * (y * z)))) * x
-- Conclusion: x = (y * (y * y)) * ((y * y) * x)
-- Original submission SHA-256: 7c3896389bdc743bacad646346b8bcc7a2a0677618337565c542f97a65d31ada
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (w ◇ (y ◇ z)))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ (q2 ◇ (q1 ◇ q2))) ◇ q0) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q0) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => q2 ◇ t) ((h (q1 ◇ q2) q0 q0 q0).symm)))).symm).trans ((h q0 q1 q2 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))).symm)
  have apc1 : forall (q3 q4 q5 q6 q7:G), ((q5 ◇ (q3 ◇ q5)) ◇ q4) = q4:=by
    intro q3 q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ q4) (congrArg (fun t => q5 ◇ t) (congrArg (fun t => q3 ◇ t) (apc0 q5 q6 q7)))).symm).trans (((congrArg (fun t => t ◇ q4) (apc0 (q5 ◇ (q3 ◇ ((q6 ◇ (q7 ◇ (q6 ◇ q7))) ◇ q5))) q6 q7)).symm).trans ((h q4 (q6 ◇ (q7 ◇ (q6 ◇ q7))) q5 q3).symm))
  have apc2 : forall (q8 q9 q10 q11:G), ((q9 ◇ q9) ◇ q8) = q8:=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ q8) (congrArg (fun t => q9 ◇ t) (apc0 q9 q10 q11))).symm).trans (((congrArg (fun t => t ◇ q8) (apc0 (q9 ◇ ((q10 ◇ (q11 ◇ (q10 ◇ q11))) ◇ q9)) q10 q11)).symm).trans (apc0 q8 (q10 ◇ (q11 ◇ (q10 ◇ q11))) q9))
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ x)):=((congrArg (fun t => (y ◇ (y ◇ y)) ◇ t) (apc2 x y ((y ◇ y) ◇ x) ((y ◇ y) ◇ x))).trans (apc1 y x y ((y ◇ (y ◇ y)) ◇ x) ((y ◇ (y ◇ y)) ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30023_to_22639 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_30023_to_22639
