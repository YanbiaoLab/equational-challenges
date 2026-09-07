-- Equation20552 → Equation17900
-- Recorded verdict: true
-- Premise: x = (x * y) * (((x * y) * z) * w)
-- Conclusion: x = (x * x) * (y * ((z * w) * w))
-- Original submission SHA-256: 66136c6670153db930558b0a6f20b4c4d37e9fb22c7c21000662d526edcd7029
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ (((x ◇ y) ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ x) ◇ (y ◇ ((z ◇ w) ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q1)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q0 ◇ q1) ◇ t) ((h (q0 ◇ q1) q0 q0 q0).symm)).symm).trans ((h q0 q1 q0 ((((q0 ◇ q1) ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q2 q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q2)) = q0:=by
    intro q2 q0 q1
    exact ((congrArg (fun t => (q0 ◇ q1) ◇ t) (congrArg (fun t => t ◇ q2) ((h q0 q1 q2 q2).symm))).symm).trans ((h q0 q1 (((q0 ◇ q1) ◇ q2) ◇ q2) q2).symm)
  have apc2 : forall (q3 q4:G), (q3 ◇ q4) = (q3 ◇ q3):=by
    intro q3 q4
    exact (((congrArg (fun t => q3 ◇ t) (apc1 q4 q3 q4)).symm).trans (((congrArg (fun t => t ◇ ((q3 ◇ q4) ◇ (q3 ◇ q4))) (apc0 q3 q4)).symm).trans (apc0 (q3 ◇ q4) (q3 ◇ q4)))).symm
  have apc3 : forall (q2 q0 q1 q3 q4:G), ((q0 ◇ q0) ◇ (q0 ◇ q2)) = q0:=by
    intro q2 q0 q1 q3 q4
    exact ((congrArg (fun t => t ◇ (q0 ◇ q2)) (apc2 q0 q1)).symm).trans (apc1 q2 q0 q1)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ x) ◇ (y ◇ ((z ◇ w) ◇ w))):=(((congrArg (fun t => (x ◇ x) ◇ t) (apc2 y ((z ◇ w) ◇ w))).trans (apc2 (x ◇ x) (y ◇ y))).trans (apc3 x x ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20552_to_17900 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20552_to_17900
