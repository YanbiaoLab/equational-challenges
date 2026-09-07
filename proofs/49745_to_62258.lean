-- Equation49745 → Equation62258
-- Recorded verdict: true
-- Premise: x * y = (x * (z * (z * w))) * x
-- Conclusion: (x * y) * z = ((x * w) * x) * z
-- Original submission SHA-256: 4dd48ff47af8025bddc32c405e7a91c72cc01e6c9c748f30ff51bf053ff447ef
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ (z ◇ (z ◇ w))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = ((x ◇ w) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1:G), ((q0 ◇ q0) ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((congrArg (fun t => t ◇ q0) (apc0 q0 (q0 ◇ (q0 ◇ q0)) q0 q0)).symm).trans ((h q0 q1 q0 q0).symm)).trans (apc0 q0 q1 (q0 ◇ q1) (q0 ◇ q1))
  have apc2 : forall (q2 q3 q4:G), ((q3 ◇ q3) ◇ (q3 ◇ q3)) = ((q3 ◇ q3) ◇ q2):=by
    intro q2 q3 q4
    exact (((congrArg (fun t => t ◇ (q3 ◇ (q3 ◇ q4))) (apc0 q3 (q3 ◇ q4) (q3 ◇ (q3 ◇ q4)) (q3 ◇ (q3 ◇ q4)))).trans (congrArg (fun t => (q3 ◇ q3) ◇ t) (apc0 q3 (q3 ◇ q4) (q3 ◇ (q3 ◇ q4)) (q3 ◇ (q3 ◇ q4))))).symm).trans ((((apc1 (q3 ◇ (q3 ◇ q4)) q4).symm).trans ((h (q3 ◇ (q3 ◇ q4)) q2 q3 q4).symm)).trans (congrArg (fun t => t ◇ q2) (apc0 q3 (q3 ◇ q4) (q3 ◇ (q3 ◇ q4)) (q3 ◇ (q3 ◇ q4)))))
  have apc3 : forall (q4 q2 q3:G), ((q3 ◇ q3) ◇ q2) = (q3 ◇ q3):=by
    intro q4 q2 q3
    exact (((apc2 q2 q3 q4).symm).trans (apc2 q3 q3 q4)).trans (apc1 q3 ((q3 ◇ q3) ◇ q3))
  exact (calc
    ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=congrArg (fun t => t ◇ z) (apc0 x y w w)
    _ = (((x ◇ x) ◇ x) ◇ z):=congrArg (fun t => t ◇ z) ((apc3 w x x).symm)
    _ = (((x ◇ w) ◇ x) ◇ z):=(congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ x) (apc0 x w w w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49745_to_62258 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49745_to_62258
