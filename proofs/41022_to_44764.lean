-- Equation41022 → Equation44764
-- Recorded verdict: true
-- Premise: x = ((((y * y) * x) * y) * z) * x
-- Conclusion: x * y = z * ((y * (y * y)) * y)
-- Original submission SHA-256: 620fd3ae2fbefbf1ae427d22a38a6f7c8f1a0b366afa28e2bfa144047fa7eb01
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((((y ◇ y) ◇ x) ◇ y) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((y ◇ (y ◇ y)) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0:G), ((q0 ◇ q0) ◇ q0) = q0:=by
    intro q0
    exact ((congrArg (fun t => t ◇ q0) ((h (q0 ◇ q0) q0 (q0 ◇ q0)).symm)).symm).trans ((h q0 (q0 ◇ q0) (q0 ◇ q0)).symm)
  have apc1 : forall (q1 q2:G), (((q1 ◇ q1) ◇ q2) ◇ q1) = q1:=by
    intro q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ q1) (apc0 q1)))).symm).trans ((h q1 q1 q2).symm)
  have apc3 : forall (q3 q4:G), (q4 ◇ q3) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (apc1 q3 q4)).symm).trans ((((congrArg (fun t => t ◇ (((q3 ◇ q3) ◇ q4) ◇ q3)) ((h q4 q3 (((q3 ◇ q3) ◇ q4) ◇ q3)).symm)).symm).trans (apc1 (((q3 ◇ q3) ◇ q4) ◇ q3) q4)).trans (apc1 q3 q4))
  exact (calc
    (x ◇ y) = y:=apc3 y x
    _ = (z ◇ ((y ◇ (y ◇ y)) ◇ y)):=((((congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => y ◇ t) (apc3 y y)))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ y) (apc3 y y)))).trans (congrArg (fun t => z ◇ t) (apc3 y y))).trans (apc3 y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41022_to_44764 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41022_to_44764
