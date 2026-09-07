-- Equation3002 → Equation17380
-- Recorded verdict: true
-- Premise: x = ((y * (z * y)) * w) * x
-- Conclusion: x = (y * y) * (y * (y * (z * x)))
-- Original submission SHA-256: a4962bc8db82e3454fefbf24ab0d6966f6137fd71fe5674e9f37242950f41d99
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ y)) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (y ◇ (y ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) ((h q0 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ q0)))).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ q0)) q0 q0).symm)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ y) ◇ (y ◇ (y ◇ (z ◇ x)))):=(((((congrArg (fun t => (y ◇ y) ◇ t) (congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) (apc0 z x)))).trans (congrArg (fun t => (y ◇ y) ◇ t) (congrArg (fun t => y ◇ t) (apc0 y x)))).trans (congrArg (fun t => (y ◇ y) ◇ t) (apc0 y x))).trans (congrArg (fun t => t ◇ x) (apc0 y y))).trans (apc0 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3002_to_17380 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3002_to_17380
