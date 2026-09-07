-- Equation45097 → Equation41653
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (((x ◇ x) ◇ z) ◇ z)
-- Conclusion: x ◇ x = y ◇ (y ◇ (z ◇ (w ◇ w)))
-- Original submission SHA-256: 49edece13bdd2b7efc7cb02cfe1dbf928eadce7db4e75b13469475d335da2922
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (((x ◇ x) ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (y ◇ (z ◇ (w ◇ w)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have p0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q0) ◇ q0)) q0).symm)).symm).trans ((h q1 q2 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have p1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((p0 q0 q1 q2).symm).trans (p0 q0 q0 q2)
  have p2 : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q1))) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q1)) (p1 q0 (q1 ◇ q1) q0))).symm).trans ((h q1 q2 (q1 ◇ q1)).symm)
  have p3 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((congrArg (fun t => q1 ◇ t) (p2 q0 q0 (q0 ◇ q0))).symm).trans (p2 q0 (q0 ◇ q0) q1)).symm
  have p4 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((p3 q0 q1).symm).trans (p3 q0 q0)
  have p5 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q1 ◇ q1))) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (p4 q1 (q0 ◇ q0))).symm).trans (p2 q0 q1 q2)
  have p6 : forall (x y z:G), (y ◇ (((x ◇ x) ◇ z) ◇ z)) = (x ◇ (((x ◇ x) ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p7 : forall (x y z:G), (x ◇ (((x ◇ x) ◇ x) ◇ x)) = (x ◇ x):=by
    intro x y z
    exact ((h x x x).trans (p6 x x x)).symm
  have p8 : forall (q0:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact (((p5 ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))) q0 (q0 ◇ q0)).symm).trans ((((congrArg (fun t => (q0 ◇ q0) ◇ t) (p4 q0 (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)))).symm).trans (p7 (q0 ◇ q0) q0 q0)).trans (p4 q0 (q0 ◇ q0)))).symm
  have p9 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact (p4 q0 q1).trans (p8 q0)
  exact (calc
    (x ◇ x) = (y ◇ (x ◇ x)):=(p9 x y).symm
    _ = (y ◇ (y ◇ (x ◇ x))):=congrArg (fun t => y ◇ t) ((p9 x y).symm)
    _ = (y ◇ (y ◇ (w ◇ w))):=(congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) (p1 x w w))).symm
    _ = (y ◇ (y ◇ (z ◇ (w ◇ w)))):=(congrArg (fun t => y ◇ t) (congrArg (fun t => y ◇ t) (p9 w z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45097_to_41653 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45097_to_41653
