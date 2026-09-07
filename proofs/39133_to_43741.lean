-- Equation39133 → Equation43741
-- Recorded verdict: true
-- Premise: x = (((y * x) * (x * z)) * w) * x
-- Conclusion: x * y = y * ((z * y) * (w * y))
-- Original submission SHA-256: c8f6a5dc791818871db44d93fc32fb03aae8ffd5886051515043de401ff4193d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ x) ◇ (x ◇ z)) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ y) ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc1 : forall (q0 q1 q2:G), (((q1 ◇ q2) ◇ q0) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q0) ((h (q1 ◇ q2) q0 q0 q1).symm))).symm).trans ((h q1 ((q0 ◇ (q1 ◇ q2)) ◇ ((q1 ◇ q2) ◇ q0)) q2 q0).symm)
  have apc2 : forall (q3 q4:G), (q3 ◇ q4) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q4) (apc1 (q4 ◇ q3) q3 q4)).symm).trans ((h q4 q3 q3 q3).symm)
  exact (calc
    (x ◇ y) = y:=apc2 x y
    _ = (y ◇ ((z ◇ y) ◇ (w ◇ y))):=((((congrArg (fun t => y ◇ t) (congrArg (fun t => (z ◇ y) ◇ t) (apc2 w y))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ y) (apc2 z y)))).trans (congrArg (fun t => y ◇ t) (apc2 y y))).trans (apc2 y y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_39133_to_43741 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_39133_to_43741
