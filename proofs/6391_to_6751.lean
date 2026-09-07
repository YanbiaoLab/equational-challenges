-- Equation6391 → Equation6751
-- Recorded verdict: true
-- Premise: x = y * (z * (w * ((w * y) * x)))
-- Conclusion: x = y * (x * ((z * y) * (z * x)))
-- Original submission SHA-256: 68f2f2c6968df1e8b156916b5c736aadce73b2c64c6d4688de618df6a12f6d0f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (w ◇ ((w ◇ y) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((z ◇ y) ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q0 ◇ ((q0 ◇ q2) ◇ q1)) = (q3 ◇ (q4 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q4 ◇ t) ((h q1 q2 (q2 ◇ q3) q0).symm))).symm).trans ((h (q0 ◇ ((q0 ◇ q2) ◇ q1)) q3 q4 q2).symm)).symm
  have apc1 : forall (q5 q6 q7 q8 q9:G), (q8 ◇ (q9 ◇ (q5 ◇ (q6 ◇ q7)))) = q7:=by
    intro q5 q6 q7 q8 q9
    exact ((congrArg (fun t => q8 ◇ t) (congrArg (fun t => q9 ◇ t) (apc0 q5 q7 q8 q5 q6))).symm).trans ((h q7 q8 q9 q5).symm)
  exact (calc
    x = x:=rfl
    _ = (y ◇ (x ◇ ((z ◇ y) ◇ (z ◇ x)))):=(apc1 (z ◇ y) z x y x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6391_to_6751 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6391_to_6751
