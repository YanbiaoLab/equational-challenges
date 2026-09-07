-- Equation30498 → Equation2430
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ ((x ◇ y) ◇ z))) ◇ x
-- Conclusion: x = (y ◇ (z ◇ (w ◇ w))) ◇ x
-- Original submission SHA-256: aacfe0b779b3ae303af110890dbb64ea08e0dd4f73ca883d77394e4c336c8d4d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ ((x ◇ y) ◇ z))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (w ◇ w))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((y ◇ (y ◇ ((x ◇ y) ◇ z))) ◇ x) = ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p1 : forall (x y z:G), ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (p0 x x x)).symm
  have p2 : forall (q0 q1 q2:G), (((q1 ◇ ((q2 ◇ q1) ◇ q0)) ◇ ((q1 ◇ ((q2 ◇ q1) ◇ q0)) ◇ q2)) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ ((q2 ◇ q1) ◇ q0)) ◇ t) (cg (fun t => (q1 ◇ ((q2 ◇ q1) ◇ q0)) ◇ t) ((h q2 q1 q0).symm)))).symm).trans ((h q1 (q1 ◇ ((q2 ◇ q1) ◇ q0)) q2).symm)
  have p3 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q2 ◇ (q2 ◇ q3))) ◇ (q0 ◇ (q0 ◇ ((q2 ◇ q0) ◇ q1)))) = (q0 ◇ (q0 ◇ ((q2 ◇ q0) ◇ q1))):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q0 ◇ (q0 ◇ ((q2 ◇ q0) ◇ q1)))) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q3) ((h q2 q0 q1).symm))))).symm).trans ((h (q0 ◇ (q0 ◇ ((q2 ◇ q0) ◇ q1))) q2 q3).symm)
  have p4 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q0 ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q0) ◇ q1)))) = (q0 ◇ (q0 ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q0) ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q0) ◇ q1)))) (cg (fun t => (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ t) (p1 q2 ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2) ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)))).trans (cg (fun t => t ◇ (q0 ◇ (q0 ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q0) ◇ q1)))) (p1 q2 ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2) ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)))).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q0) ◇ q1)))) (cg (fun t => (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ t) (cg (fun t => (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ t) (p1 q2 q0 q0)))).symm).trans (p3 q0 q1 (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) q2))
  have p5 : forall (q0 q1:G), (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) = (q0 ◇ (q0 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact (((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q1) ((h q0 q0 q0).symm))))).symm).trans (p4 q0 q1 q0)).trans (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q1) (p1 q0 ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0) ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)))))
  have p6 : forall (q0 q1 q2:G), (((q1 ◇ q2) ◇ ((q1 ◇ q2) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q1 ◇ q2)) ◇ q0))) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q1) (p4 (q1 ◇ q2) q0 q2)).symm).trans (((cg (fun t => t ◇ q1) (cg (fun t => q2 ◇ t) (p4 (q1 ◇ q2) q0 q2))).symm).trans ((h q1 q2 ((q1 ◇ q2) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q1 ◇ q2)) ◇ q0))).symm))
  have p7 : forall (q0 q1 q2:G), (((q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ ((q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ ((q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ q2))) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ q2) (p5 q1 q0))))).symm).trans ((h q1 (q1 ◇ (q1 ◇ (q1 ◇ q0))) q2).symm)
  have p8 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q2 ◇ (q2 ◇ q3))) ◇ ((q2 ◇ ((q1 ◇ q2) ◇ q0)) ◇ ((q2 ◇ ((q1 ◇ q2) ◇ q0)) ◇ q1))) = ((q2 ◇ ((q1 ◇ q2) ◇ q0)) ◇ ((q2 ◇ ((q1 ◇ q2) ◇ q0)) ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q2 ◇ ((q1 ◇ q2) ◇ q0)) ◇ ((q2 ◇ ((q1 ◇ q2) ◇ q0)) ◇ q1))) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q3) (p2 q0 q2 q1))))).symm).trans ((h ((q2 ◇ ((q1 ◇ q2) ◇ q0)) ◇ ((q2 ◇ ((q1 ◇ q2) ◇ q0)) ◇ q1)) q2 q3).symm)
  have p9 : forall (q1 q2 q3 q0:G), ((q2 ◇ (q2 ◇ (q2 ◇ q3))) ◇ q1) = q1:=by
    intro q1 q2 q3 q0
    exact ((((cg (fun t => (q2 ◇ (q2 ◇ (q2 ◇ q3))) ◇ t) (cg (fun t => ((q1 ◇ q2) ◇ ((q1 ◇ q2) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q1 ◇ q2)) ◇ q0))) ◇ t) (cg (fun t => t ◇ q1) (p4 (q1 ◇ q2) q0 q2)))).trans (cg (fun t => (q2 ◇ (q2 ◇ (q2 ◇ q3))) ◇ t) (cg (fun t => ((q1 ◇ q2) ◇ ((q1 ◇ q2) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q1 ◇ q2)) ◇ q0))) ◇ t) (p6 q0 q1 q2)))).trans (cg (fun t => (q2 ◇ (q2 ◇ (q2 ◇ q3))) ◇ t) (p6 q0 q1 q2))).symm).trans ((((cg (fun t => (q2 ◇ (q2 ◇ (q2 ◇ q3))) ◇ t) (cg (fun t => t ◇ ((q2 ◇ ((q1 ◇ q2) ◇ ((q1 ◇ q2) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q1 ◇ q2)) ◇ q0)))) ◇ q1)) (p4 (q1 ◇ q2) q0 q2))).symm).trans (p8 ((q1 ◇ q2) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q1 ◇ q2)) ◇ q0)) q1 q2 q3)).trans ((((cg (fun t => (q2 ◇ ((q1 ◇ q2) ◇ ((q1 ◇ q2) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q1 ◇ q2)) ◇ q0)))) ◇ t) (cg (fun t => t ◇ q1) (p4 (q1 ◇ q2) q0 q2))).trans (cg (fun t => (q2 ◇ ((q1 ◇ q2) ◇ ((q1 ◇ q2) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q1 ◇ q2)) ◇ q0)))) ◇ t) (p6 q0 q1 q2))).trans (cg (fun t => t ◇ q1) (p4 (q1 ◇ q2) q0 q2))).trans (p6 q0 q1 q2)))
  have pa : forall (q0 q1 q2 q3:G), (q2 ◇ q1) = q1:=by
    intro q0 q1 q2 q3
    exact ((((cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (p9 q2 q1 q0 ((q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ q2))))).trans (cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (p9 q2 q1 q0 ((q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ q2))))).trans (cg (fun t => t ◇ q1) (p9 q2 q1 q0 ((q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ q2)))).symm).trans (p7 q0 q1 q2)
  exact (pa x x (y ◇ (z ◇ (w ◇ w))) x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30498_to_2430 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_30498_to_2430
