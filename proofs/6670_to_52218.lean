-- Equation6670 → Equation52218
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((x ◇ y) ◇ (z ◇ z)))
-- Conclusion: x ◇ x = ((y ◇ (z ◇ z)) ◇ y) ◇ y
-- Original submission SHA-256: 0aa5f775a0fbec7c930bce4d19de402f147dba6a6f5f9110b41ae134f2e29739
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ y) ◇ (z ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ (z ◇ z)) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), (y ◇ (x ◇ ((x ◇ y) ◇ (z ◇ z)))) = (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p1 : forall (q0:G), (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = q0:=by
    intro q0
    exact ((p0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have p2 : forall (q0 q1:G), ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q1)))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (p1 q0)))).symm).trans ((h q0 (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) q1).symm)
  have p3 : forall (q0:G), ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) ((h q0 q0 q0).symm)).symm).trans (p2 q0 (q0 ◇ q0))
  have p4 : forall (q0:G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p3 (q0 ◇ q0)))).symm).trans ((h (q0 ◇ q0) (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) q0).symm)
  have p5 : forall (q0 q1 q2 q3:G), ((q0 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q1))) ◇ (q2 ◇ (q0 ◇ (q3 ◇ q3)))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q0 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q1))) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q3 ◇ q3)) ((h q0 q2 q1).symm)))).symm).trans ((h q2 (q0 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q1))) q3).symm)
  have p6 : forall (q0 q1:G), ((q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) ◇ t) ((h q1 q1 q1).symm)).symm).trans (p5 q1 q0 q1 (q1 ◇ q1))
  have p7 : forall (q0:G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (p4 q0))).symm).trans (p6 (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)))
  have p8 : forall (q0:G), ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (p7 q0))).symm).trans ((h ((q0 ◇ q0) ◇ (q0 ◇ q0)) (q0 ◇ q0) (q0 ◇ q0)).symm)
  have p9 : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (p8 q0)).symm).trans ((h (q0 ◇ q0) (q0 ◇ q0) (q0 ◇ q0)).symm)
  have pa : forall (q0:G), (q0 ◇ (q0 ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p9 q0))).symm).trans ((h q0 q0 (q0 ◇ q0)).symm)
  have pb : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (p9 q0)).symm).trans (pa (q0 ◇ q0))
  have pc : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (cg (fun t => t ◇ (q0 ◇ q0)) (pb q1))).trans (cg (fun t => ((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ t) (pb q1))).symm).trans (((cg (fun t => (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p6 q0 (q1 ◇ q1)))).symm).trans ((h (q1 ◇ q1) (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ (q0 ◇ q0)) q1).symm))
  have pd : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (pb q1)).symm).trans (((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (pc q0 q1))).symm).trans ((h (q1 ◇ q1) (q0 ◇ q0) q1).symm))
  have pe : forall (q0 q2 q1:G), (q2 ◇ q2) = (q0 ◇ q0):=by
    intro q0 q2 q1
    exact ((((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pd q1 q2))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (pd q0 q2))).trans (pd q1 q2)).symm).trans (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ (q2 ◇ q2)) (pd q0 q1)))).symm).trans ((h (q0 ◇ q0) (q1 ◇ q1) q2).symm))
  have pf : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q0)) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => q1 ◇ t) (pd q1 q0))).symm).trans (((cg (fun t => (q1 ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) ◇ t) ((h q1 q1 q1).symm)).symm).trans (p5 q1 q0 q1 (q1 ◇ q1)))
  exact (pe y x x).trans ((cg (fun t => t ◇ y) (pf z y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6670_to_52218 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6670_to_52218
