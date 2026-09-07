-- Equation9237 → Equation33712
-- Recorded verdict: true
-- Premise: x = x * ((y * z) * (y * (w * z)))
-- Conclusion: x = ((x * y) * (x * (z * y))) * x
-- Original submission SHA-256: c4dac8a527ecd63b59cf3935111641cda4c35aa945d0b043bbc22134789b8ae2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ z) ◇ (y ◇ (w ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ (x ◇ (z ◇ y))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q2 ◇ q1) ◇ (q0 ◇ q1))) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) ((h ((q2 ◇ q1) ◇ (q0 ◇ q1)) q2 q1 q0).symm)).symm).trans ((h q3 (q2 ◇ q1) (q0 ◇ q1) q2).symm)
  have apc1 : forall (q4 q5 q6 q7 q8 q9:G), (q6 ◇ (q5 ◇ q4)) = q6:=by
    intro q4 q5 q6 q7 q8 q9
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => q5 ◇ t) (apc0 q7 q8 q9 q4))).symm).trans (((congrArg (fun t => q6 ◇ t) (congrArg (fun t => t ◇ (q4 ◇ ((q9 ◇ q8) ◇ (q7 ◇ q8)))) (apc0 q7 q8 q9 q5))).symm).trans (apc0 q4 ((q9 ◇ q8) ◇ (q7 ◇ q8)) q5 q6))
  have apc2 : forall (q10 q11:G), (q11 ◇ q10) = q11:=by
    intro q10 q11
    exact ((congrArg (fun t => q11 ◇ t) (apc1 q10 q10 q10 q10 q10 q10)).symm).trans (apc1 (q10 ◇ q10) q10 q11 q10 q10 q10)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ y) ◇ (x ◇ (z ◇ y))) ◇ x):=(((((congrArg (fun t => t ◇ x) (congrArg (fun t => (x ◇ y) ◇ t) (congrArg (fun t => x ◇ t) (apc2 y z)))).trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ (x ◇ z)) (apc2 y x)))).trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (apc2 z x)))).trans (congrArg (fun t => t ◇ x) (apc2 x x))).trans (apc2 x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9237_to_33712 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_9237_to_33712
