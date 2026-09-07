-- Equation6678 → Equation45190
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
-- Conclusion: x ◇ x = y ◇ (((z ◇ y) ◇ z) ◇ z)
-- Original submission SHA-256: b2b1e2f547eb817452249861b27043a5fe6806431338299127279419cb3d9d2a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (((z ◇ y) ◇ z) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1:G), (((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ (q1 ◇ (q1 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ t) ((h (q1 ◇ (q1 ◇ q0)) q1 q0).symm)).symm).trans ((h q1 ((q1 ◇ (q1 ◇ q0)) ◇ q0) (q1 ◇ q0)).symm)
  have p1 : forall (q0 q1:G), ((q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q1 ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ((h q1 q1 q0).symm))).symm).trans (p0 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q1)
  have p2 : forall (q0 q1:G), ((q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) ((h q1 q1 q0).symm)).symm).trans (p1 q0 q1)
  have p3 : forall (q0 q1:G), (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ ((q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ q1))) (cg (fun t => t ◇ q1) (p2 q0 q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (p2 q0 q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (p2 q0 q1))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ q1))) (cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (p2 q0 q1)))).symm).trans (p0 q1 (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))))).symm
  have p4 : forall (q1 q0:G), (((q1 ◇ q1) ◇ q1) ◇ q1) = q1:=by
    intro q1 q0
    exact ((cg (fun t => t ◇ q1) (p3 q0 q1)).symm).trans (p2 q0 q1)
  have p5 : forall (x y z:G), (y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))) = (x ◇ ((x ◇ x) ◇ x)):=by
    intro x y z
    exact (((h x y z).symm).trans (h x x x)).trans (cg (fun t => x ◇ t) (p3 x x))
  have p6 : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (p3 q0 q0)).symm).trans ((h q0 q0 q0).symm)
  have p7 : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ (q0 ◇ (q3 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q3 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))) ((h q0 q2 q1).symm)))).symm).trans ((h q2 q3 (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))).symm)
  have p8 : forall (q2 q3 q0 q1:G), (q3 ◇ (q2 ◇ q2)) = ((q3 ◇ q3) ◇ q3):=by
    intro q2 q3 q0 q1
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) (p7 q0 q1 q2 q3))).symm).trans (((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ (q3 ◇ (q2 ◇ (q0 ◇ (q3 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))))) (p7 q0 q1 q2 q3))).symm).trans (p3 (q2 ◇ (q0 ◇ (q3 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) q3))
  have p9 : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) (p4 (q0 ◇ q0) ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)))).symm).trans (((cg (fun t => t ◇ (q0 ◇ q0)) (cg (fun t => t ◇ (q0 ◇ q0)) (p8 q0 (q0 ◇ q0) q0 q0))).symm).trans (p4 (q0 ◇ q0) q0))
  have pa : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (p6 q0))).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (cg (fun t => q0 ◇ t) (p6 q0)))).symm).trans (p0 ((q0 ◇ q0) ◇ q0) q0))
  have pb : forall (q0 q1 q2:G), (q2 ◇ (((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ (q1 ◇ (q2 ◇ (q1 ◇ (q1 ◇ q0)))))) = ((q1 ◇ (q1 ◇ q0)) ◇ q0):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => ((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ t) (cg (fun t => t ◇ (q2 ◇ (q1 ◇ (q1 ◇ q0)))) (p0 q0 q1)))).symm).trans ((h ((q1 ◇ (q1 ◇ q0)) ◇ q0) q2 (q1 ◇ (q1 ◇ q0))).symm)
  have pc : forall (q0:G), ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) = (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => q0 ◇ t) (p4 q0 (((q0 ◇ q0) ◇ q0) ◇ q0)))).symm).trans (((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ q0)) (p4 q0 q0))).symm).trans (p3 q0 ((q0 ◇ q0) ◇ q0)))).symm
  have pd : forall (q0:G), ((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pc q0)).symm).trans (p4 ((q0 ◇ q0) ◇ q0) q0)
  have pe : forall (q0 q1:G), (q1 ◇ (q0 ◇ (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (p8 q1 (q0 ◇ q1) q0 q0))).symm).trans ((h q0 q1 q1).symm)
  have pf : forall (q0:G), ((((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = q0:=by
    intro q0
    exact (((pa q0).symm).trans (p8 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) q0 q0)).symm
  have pg : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pf q0))).symm).trans (pe (q0 ◇ q0) ((q0 ◇ q0) ◇ q0))
  have ph : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0)).symm).trans (pc q0)).symm
  have pi : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = q0:=by
    intro q0
    exact ((((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (pg q0)).trans (pa q0)).symm).trans ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0))).symm).trans (ph ((q0 ◇ q0) ◇ q0))).trans ((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (pg q0))))).symm
  have pj : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0))).symm).trans ((((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0))).symm).trans (pg ((q0 ◇ q0) ◇ q0))).trans (pg q0))
  have pk : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0))).symm).trans (p4 ((q0 ◇ q0) ◇ q0) q0)
  have pl : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (pf q0)).symm).trans (p4 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) q0)
  have pm : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))) = ((q2 ◇ q2) ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))) (p6 q0))).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))) (p5 q0 q2 q1))).symm).trans (p3 (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))) q2))
  have pn : forall (q0 q1:G), (q1 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0)))) = q0:=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (pi q0))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) (p6 q0)))).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q1 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pi q0)))).symm).trans (pb ((q0 ◇ q0) ◇ q0) (q0 ◇ q0) q1)).trans ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pi q0)).trans (p6 q0)))
  have po : forall (q1 q2 q0:G), (q2 ◇ (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ (q2 ◇ q1)))) = ((q1 ◇ q1) ◇ q1):=by
    intro q1 q2 q0
    exact ((((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (p8 (q1 ◇ q0) q1 (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))))))).trans (cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (p6 q1)))))).trans (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q1 ◇ (q2 ◇ q1))) (p8 (q1 ◇ q0) q1 (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))))).symm).trans ((((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => t ◇ (q2 ◇ (q1 ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))))) (p1 q0 q1)))).symm).trans ((h (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) q2 (q1 ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))).symm)).trans (p8 (q1 ◇ q0) q1 (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))))
  have pp : forall (q0:G), ((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) = ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0
    exact ((((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0)))).trans (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (pg q0)))).trans (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (pa q0))).symm).trans ((((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pd q0)))).symm).trans (po ((q0 ◇ q0) ◇ q0) (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) q0)).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0)))
  have pq : forall (q0:G), ((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (pi q0))).symm).trans (((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pp q0)))).symm).trans (pn q0 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))))
  have pr : forall (q0:G), (((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact (((pq q0).symm).trans (p8 q0 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) q0 q0)).symm
  have ps : forall (q0:G), ((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact (((cg (fun t => q0 ◇ t) (pr q0)).symm).trans (((cg (fun t => t ◇ (((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)))) (pr q0)).symm).trans (pg (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))))).symm
  have pt : forall (q0:G), ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact ((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) (ps q0)).symm).trans (pr q0)
  have pu : forall (q1 q2 q0:G), (((q1 ◇ q1) ◇ q1) ◇ (q2 ◇ ((q2 ◇ q1) ◇ q1))) = q2:=by
    intro q1 q2 q0
    exact ((((cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (p8 (q1 ◇ q0) q1 (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))))))).trans (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => q2 ◇ t) (p6 q1)))))).trans (cg (fun t => t ◇ (q2 ◇ ((q2 ◇ q1) ◇ q1))) (p8 (q1 ◇ q0) q1 (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))))).symm).trans (((cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => (q2 ◇ (q1 ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))) ◇ t) (p1 q0 q1)))).symm).trans ((h q2 (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (q1 ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))).symm))
  have pv : forall (q0 q1:G), ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) = q1:=by
    intro q0 q1
    exact ((((((((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (p8 q0 q1 (q1 ◇ (q0 ◇ q0)) (q1 ◇ (q0 ◇ q0))))))).trans (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (cg (fun t => ((q1 ◇ q1) ◇ q1) ◇ t) (p8 q0 q1 (q1 ◇ (q0 ◇ q0)) (q1 ◇ (q0 ◇ q0)))))))).trans (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (((q1 ◇ q1) ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (p8 q0 q1 (q1 ◇ (q0 ◇ q0)) (q1 ◇ (q0 ◇ q0))))))).trans (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (pg q1))))).trans (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))) (cg (fun t => t ◇ (q0 ◇ q0)) (p9 q0)))).trans (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))) (p9 q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pl q1))).symm).trans (((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (p8 q0 (q1 ◇ (q0 ◇ q0)) q0 q0))).symm).trans (pu (q0 ◇ q0) q1 q0))
  have pw : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((((cg (fun t => ((((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pl q1))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) (pj q1)))).trans (cg (fun t => ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) ◇ t) (pv q0 q1))).trans (cg (fun t => t ◇ q1) (pv q1 q1))).symm).trans (((cg (fun t => ((((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) (pv q0 q1)))).symm).trans (pu ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) (q0 ◇ q0) q0))
  have px : forall (q0 q1:G), ((q1 ◇ q1) ◇ q0) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (pv q0 q0))).symm).trans (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0))) (pg q0))).symm).trans (pv q1 ((q0 ◇ q0) ◇ q0)))
  have py : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (pw q0 q1))).symm).trans (p6 q1)
  have pz : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (pw q0 q1))).symm).trans (p4 q1 q0)
  have p10 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q0)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ q2) ◇ t) (pw q0 q2)))).symm).trans ((h q1 q2 q2).symm)
  have p11 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ q2)) (pw q0 (q1 ◇ q2))))).symm).trans (pe q1 q2)
  have p12 : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = (((q0 ◇ q0) ◇ q1) ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ q1) (pw q0 q1))).symm).trans (ph q1)).symm
  have p13 : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)):=by
    intro q0 q1
    exact ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (cg (fun t => t ◇ q1) (pj q1)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pk q1))).symm).trans (((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (cg (fun t => (((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) ◇ t) (pv q0 q1)))).symm).trans (pn ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) (q0 ◇ q0)))).symm
  have p14 : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)) = (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) (ps q0)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pt q0)))).symm).trans (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ (((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)))) (ps q0))).symm).trans (pv q1 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))))
  have p15 : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (cg (fun t => t ◇ q1) (pw q0 q1))).symm).trans (pg q1)
  have p16 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)) = (((q1 ◇ q1) ◇ q2) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((((cg (fun t => ((q1 ◇ q1) ◇ q2) ◇ t) (pw q0 q2)).symm).trans ((p12 q1 q2).symm)).trans (p14 q2 q2)).symm
  have p17 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q2)) = (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q2) (pw q0 q2))).symm).trans ((p13 q1 q2).symm)).trans (p14 q2 q2)
  have p18 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2)) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q2) ◇ t) (cg (fun t => t ◇ q2) (pw q0 q2))).symm).trans (p15 q1 q2)
  have p19 : forall (q1 q2 q0:G), ((q1 ◇ q1) ◇ (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2))) = q2:=by
    intro q1 q2 q0
    exact ((cg (fun t => (q1 ◇ q1) ◇ t) (p17 q2 q0 q2)).symm).trans (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ ((q2 ◇ q2) ◇ q2)) (pw q0 q2))).symm).trans (pv q1 q2))
  have p1a : forall (q0 q2 q1:G), (((q2 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q2 ◇ q2)) = q2:=by
    intro q0 q2 q1
    exact ((cg (fun t => t ◇ (q2 ◇ q2)) (cg (fun t => (q2 ◇ q0) ◇ t) (px q0 q1))).symm).trans (((cg (fun t => ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ t) (cg (fun t => q2 ◇ t) ((h q2 (q1 ◇ q1) q0).symm))).symm).trans (p11 q1 q2 ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0))))
  have p1b : forall (q0 q1:G), ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) = (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact ((((((((cg (fun t => t ◇ (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (p9 q1)))).trans (cg (fun t => t ◇ (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))) (cg (fun t => q1 ◇ t) (p9 q1)))).trans (cg (fun t => t ◇ (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))) (p8 q1 q1 (q1 ◇ (q1 ◇ q1)) (q1 ◇ (q1 ◇ q1))))).trans (p8 ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ((q1 ◇ q1) ◇ q1) (((q1 ◇ q1) ◇ q1) ◇ (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))) (((q1 ◇ q1) ◇ q1) ◇ (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))))).trans (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (pg q1))).trans (p17 q1 q1 q1)).symm).trans (((cg (fun t => t ◇ (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ (q1 ◇ q1))) (p1a q0 q1 q0))).symm).trans (p1a (q1 ◇ q1) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) q0))).symm
  have p1c : forall (q0 q1:G), (((q0 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q1)) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (p1a q0 q1 q0))).symm).trans (p10 q1 (q1 ◇ q0) ((q0 ◇ q0) ◇ q0))
  have p1d : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)) = (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q2 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (pw q0 q1))).symm).trans (p1b q1 q2)
  have p1e : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ q1) ◇ ((q2 ◇ q1) ◇ q2)) = (q2 ◇ q1):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q2 ◇ q1) ◇ q2)) (cg (fun t => t ◇ q1) (pw q0 q1))).symm).trans (p1c q1 q2)
  have p1f : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q1 ◇ ((q0 ◇ q0) ◇ q2)) ◇ q2))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ ((q0 ◇ q0) ◇ q2)) ◇ t) (py q0 q2)))).symm).trans ((h q1 q2 ((q0 ◇ q0) ◇ q2)).symm)
  have p1g : forall (q0 q1 q2 q3:G), ((q2 ◇ q2) ◇ (((q1 ◇ q1) ◇ q3) ◇ (q0 ◇ q0))) = q3:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q2 ◇ q2) ◇ t) (p16 q0 q1 q3)).symm).trans (p19 q2 q3 q0)
  have p1h : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q2)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q2 ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (cg (fun t => t ◇ (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2))) (p18 q0 q0 q1)))).trans (cg (fun t => (q2 ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (p1g q2 q2 q1 q2)))).symm).trans (((cg (fun t => (q2 ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)) ◇ t) (p1d q0 q1 q2)))).symm).trans (pn ((q0 ◇ q0) ◇ q1) (q2 ◇ q1)))
  have p1i : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q1))) = q0:=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q1))) (p1c q0 q1)).symm).trans (p1d q2 ((q1 ◇ q0) ◇ q1) ((q0 ◇ q0) ◇ q0))).trans ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (p17 q0 q0 q0))).trans (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (pg q0))).trans (pq q0))
  have p1j : forall (q0 q1 q2:G), (q0 ◇ ((q2 ◇ q2) ◇ (q0 ◇ q1))) = (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q1) (pn q0 q1)))).symm).trans (((cg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q1 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0)))) ◇ q1))) (pn q0 q1)).symm).trans (p1i (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) q1 q2))
  have p1k : forall (q0 q1 q2:G), (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) = (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact ((p1j q0 q1 q2).symm).trans ((p1j q0 q1 q2).trans ((p1j q0 q1 q0).symm))
  have p1l : forall (q0 q1 q2:G), (q0 ◇ ((q2 ◇ q2) ◇ (q0 ◇ q1))) = (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (p1j q0 q1 q2).trans (p1k q0 q1 (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))))
  have p1m : forall (q0 q1 q2:G), (q1 ◇ ((q1 ◇ q1) ◇ (q1 ◇ ((q1 ◇ q0) ◇ q0)))) = q0:=by
    intro q0 q1 q2
    exact ((p1l q1 ((q1 ◇ q0) ◇ q0) q2).symm).trans ((((cg (fun t => t ◇ ((q2 ◇ q2) ◇ (q1 ◇ ((q1 ◇ q0) ◇ q0)))) (pu q0 q1 q0)).symm).trans (p1d q2 (q1 ◇ ((q1 ◇ q0) ◇ q0)) ((q0 ◇ q0) ◇ q0))).trans ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pg q0))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (p17 q0 q0 q0))).trans (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (pg q0))).trans (pq q0)))
  have p1n : forall (q0 q1:G), (((q1 ◇ q0) ◇ q0) ◇ q0) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q0) ◇ t) (p1m q0 q1 q0)).symm).trans (p11 q1 q1 ((q1 ◇ q0) ◇ q0))
  have p1o : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0)))) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q0) ◇ q0) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (p4 q0 (((q0 ◇ q0) ◇ q0) ◇ q0))))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q0) ◇ q0) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (p4 q0 (((q0 ◇ q0) ◇ q0) ◇ q0))))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0))) (cg (fun t => t ◇ q0) (p4 q0 (((q0 ◇ q0) ◇ q0) ◇ q0)))))).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ (((q0 ◇ q0) ◇ q0) ◇ (((q0 ◇ q0) ◇ q0) ◇ q0))))) (cg (fun t => t ◇ q0) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (p4 q0 q0))))).symm).trans (pb q0 ((q0 ◇ q0) ◇ q0) q1)).trans ((cg (fun t => t ◇ q0) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (p4 q0 (((q0 ◇ q0) ◇ q0) ◇ q0)))).trans (cg (fun t => t ◇ q0) (p4 q0 (((q0 ◇ q0) ◇ q0) ◇ q0)))))
  have p1p : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0)) ◇ (q0 ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (p1o q0 q1)).symm).trans (((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0))) (p1o q0 q1)))).symm).trans (p1f q0 q1 (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0))))
  have p1q : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ (q0 ◇ q0)) = (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q0 ◇ q0)) (p9 q0)))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => t ◇ q1) (p9 q0)))).trans (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (p9 q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (p1p q0 q1))).symm).trans (p1p (q0 ◇ q0) (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0))))
  have p1r : forall (q0 q1 q2:G), ((((q1 ◇ q1) ◇ q1) ◇ (q2 ◇ q1)) ◇ (q0 ◇ q0)) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q1 ◇ q1) ◇ q1) ◇ (q2 ◇ q1)) ◇ t) (pw q0 q1)).symm).trans (p1p q1 q2)
  have p1s : forall (q0 q1:G), (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)) = ((q1 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (p1h q0 q0 q1))).trans (cg (fun t => (q1 ◇ q0) ◇ t) (pg q0))).symm).trans (((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (p1r (q1 ◇ q0) q0 q1))))).symm).trans (pm ((q0 ◇ q0) ◇ q0) (q1 ◇ q0) (q1 ◇ q0)))).symm
  have p1t : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q0)))) (p1s q0 q1)).trans (p1i (q0 ◇ q0) (q1 ◇ q0) (q1 ◇ q0))).symm).trans (((cg (fun t => (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) (p1s q0 q1)))).symm).trans (pu (q1 ◇ q0) ((q1 ◇ q0) ◇ (q1 ◇ q0)) q0))).symm
  have p1u : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q1 ◇ q1)) = ((q0 ◇ q0) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q2 ◇ q1)) (pw q0 (q2 ◇ q1))).symm).trans (p1s q1 q2)).symm
  have p1v : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q1 ◇ q0)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q0 ◇ q0) ◇ t) (pz q2 (q1 ◇ q0))).symm).trans (((cg (fun t => t ◇ (((q2 ◇ q2) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))) (p1t q0 q1)).symm).trans (p1h q2 (q1 ◇ q0) (q1 ◇ q0)))).symm
  have p1w : forall (q1 q2 q0 q3:G), ((q2 ◇ q1) ◇ (q2 ◇ q2)) = ((q1 ◇ q1) ◇ (q2 ◇ q1)):=by
    intro q1 q2 q0 q3
    exact ((cg (fun t => (q2 ◇ q1) ◇ t) (p1t q2 (q2 ◇ q1))).symm).trans ((((cg (fun t => t ◇ (((q2 ◇ q1) ◇ q2) ◇ ((q2 ◇ q1) ◇ q2))) (p1e q0 q1 q2)).symm).trans (p1u q3 ((q2 ◇ q1) ◇ q2) ((q0 ◇ q0) ◇ q1))).trans ((cg (fun t => (q3 ◇ q3) ◇ t) (p1e q0 q1 q2)).trans (p1v q1 q2 q3)))
  have p1x : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q2)) = (((q1 ◇ q0) ◇ q2) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact (((cg (fun t => ((q1 ◇ q0) ◇ q2) ◇ t) (p1t q0 q1)).symm).trans (p1w q2 (q1 ◇ q0) q0 q0)).symm
  have p1y : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ q2) ◇ (((q0 ◇ q0) ◇ q1) ◇ q2)) = q1:=by
    intro q0 q1 q2
    exact (((p1r q2 q1 q1).symm).trans (((cg (fun t => t ◇ (q2 ◇ q2)) (p17 q0 q2 q1)).symm).trans (p1q q2 ((q0 ◇ q0) ◇ q1)))).symm
  have p1z : forall (q0 q1 q2 q3:G), ((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q3)) = (((q2 ◇ q1) ◇ q3) ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q2 ◇ q1) ◇ q3)) (pw q0 q3)).symm).trans (p1x q1 q2 q3)
  have p20 : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q0) ◇ (q1 ◇ q1)) ◇ (q0 ◇ q1)) = q1:=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q0)) (p1t q0 (q0 ◇ q1)))).trans (cg (fun t => t ◇ (q0 ◇ q1)) (p1z q0 q1 q0 q0))).symm).trans (((cg (fun t => ((((q0 ◇ q1) ◇ q0) ◇ ((q0 ◇ q1) ◇ q0)) ◇ ((q0 ◇ q1) ◇ q0)) ◇ t) (p1e q0 q1 q0)).symm).trans (p1y q0 q1 ((q0 ◇ q1) ◇ q0)))
  have p21 : forall (q1 q2 q0:G), ((q2 ◇ q1) ◇ q2) = (q2 ◇ (q2 ◇ q1)):=by
    intro q1 q2 q0
    exact ((((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ ((q2 ◇ q1) ◇ q2))) (cg (fun t => t ◇ (((q2 ◇ q1) ◇ q2) ◇ ((q2 ◇ q1) ◇ q2))) (p1d q0 q1 q2))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ ((q2 ◇ q1) ◇ q2))) (cg (fun t => (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)) ◇ t) (p1t q2 (q2 ◇ q1))))).trans (cg (fun t => ((((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)) ◇ (q2 ◇ q2)) ◇ t) (p1e q0 q1 q2))).trans (cg (fun t => t ◇ (q2 ◇ q1)) (pq q2))).symm).trans (((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ ((q2 ◇ q1) ◇ q2))) (cg (fun t => t ◇ (((q2 ◇ q1) ◇ q2) ◇ ((q2 ◇ q1) ◇ q2))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q1)) (p1e q0 q1 q2)))).symm).trans (p20 ((q0 ◇ q0) ◇ q1) ((q2 ◇ q1) ◇ q2)))).symm
  have p22 : forall (q0 q1:G), (q1 ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q1) (pn q0 q1)).symm).trans (p21 (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) q1 q0)).trans ((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p1k q0 q1 (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0)))))).trans (cg (fun t => q1 ◇ t) (p11 q0 q0 q1)))).symm
  have p23 : forall (q0 q1:G), (((q0 ◇ q1) ◇ q0) ◇ q0) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (p22 q0 q1))).symm).trans (p1n q0 q1)
  exact (pw y x).trans ((cg (fun t => y ◇ t) (p23 z y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6678_to_45190 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6678_to_45190
