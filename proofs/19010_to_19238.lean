-- Equation19010 → Equation19238
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
-- Conclusion: x = (y ◇ z) ◇ ((x ◇ x) ◇ (y ◇ z))
-- Original submission SHA-256: c65e20a3d1e2052cdb6054d3bea798e39dbfae0c7e9d81be8c9bea1da33396c4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((x ◇ x) ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))) = ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p1 : forall (q0 q1 q2 q3:G), (q0 ◇ ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ ((q1 ◇ q0) ◇ q3))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ ((q1 ◇ q0) ◇ q3))) ((h q0 q1 q2).symm)).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) (q1 ◇ q0) q3).symm)
  have p2 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm))).symm).trans (p1 q0 q1 q2 (q1 ◇ q0))
  have p3 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) ((p2 q0 q1 q0).symm)).symm).trans ((h q0 q1 q0).symm)
  have p4 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q1 ◇ q2)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p2 q0 q1 q2).symm).trans (p2 q0 q1 q0)
  have p5 : forall (q0 q1:G), ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (p4 q0 q1 q0)).symm).trans ((h q0 q1 q0).symm)
  have p6 : forall (q0 q1 q3 q2:G), ((q3 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => t ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) (cg (fun t => q3 ◇ t) (p4 q0 q1 q2))).symm).trans ((((cg (fun t => (q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => t ◇ (q3 ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm))).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) q3 (q1 ◇ q0)).symm)).trans (p4 q0 q1 q2))
  have p7 : forall (q0 q1 q2 q3:G), (((q1 ◇ q2) ◇ q3) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) = ((q3 ◇ q3) ◇ ((q2 ◇ q0) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q1 ◇ q2) ◇ q3) ◇ t) (p4 q0 q1 q2)).symm).trans (p4 q3 (q2 ◇ q0) (q1 ◇ q2))
  have p8 : forall (q0 q1 q3 q2:G), (q0 ◇ ((q3 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q1 ◇ q0) ◇ q3))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q3 q2
    exact (((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ q3)) (cg (fun t => q3 ◇ t) (p4 q0 q1 q2)))).trans (cg (fun t => t ◇ ((q3 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q1 ◇ q0) ◇ q3))) (p5 q0 q0))).symm).trans ((((cg (fun t => t ◇ ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ ((q1 ◇ q0) ◇ q3))) (p0 q0 q1 q2)).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) (q1 ◇ q0) q3).symm)).trans (p4 q0 q1 q2))
  have p9 : forall (q0 q1 q3 q2:G), ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q3) ◇ q0) = ((q3 ◇ q3) ◇ ((q1 ◇ q0) ◇ q3)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q3) (p4 q0 q1 q2))).symm).trans (((cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans (p4 q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))))
  have pa : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ (((q3 ◇ ((q0 ◇ q3) ◇ (q0 ◇ q3))) ◇ q2) ◇ ((q1 ◇ q3) ◇ (q0 ◇ q1)))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ q2) ◇ t) (cg (fun t => ((q3 ◇ ((q0 ◇ q3) ◇ (q0 ◇ q3))) ◇ q2) ◇ t) (p2 q3 q0 q1))).symm).trans ((h q2 q3 (q3 ◇ ((q0 ◇ q3) ◇ (q0 ◇ q3)))).symm)
  have pb : forall (q0 q1 q2 q3:G), (((q2 ◇ q0) ◇ q3) ◇ (((q1 ◇ q2) ◇ q3) ◇ (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))))) = q3:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q2 ◇ q0) ◇ q3) ◇ t) (cg (fun t => ((q1 ◇ q2) ◇ q3) ◇ t) ((p2 q0 q1 q2).symm))).symm).trans ((h q3 (q2 ◇ q0) (q1 ◇ q2)).symm)
  have pc : forall (q0 q1:G), (((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) ◇ q1) ◇ ((q1 ◇ q1) ◇ (q0 ◇ q1))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) ◇ q1) ◇ t) (p4 q1 q0 (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans (pb q0 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1)
  have pd : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p9 q0 q0 q0 q0)).symm).trans (pc q0 q0)
  have pe : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1)) = q1:=by
    intro q0 q1
    exact (((cg (fun t => (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q1) ◇ t) (p9 q0 q0 q1 ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q1) ◇ q0))).trans (p7 q1 (q0 ◇ q0) ((q0 ◇ q0) ◇ q0) q1)).symm).trans (((cg (fun t => (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q1) ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q1) ◇ t) (pd q0))).symm).trans ((h q1 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm))
  have pf : forall (q1 q0:G), (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) = q1:=by
    intro q1 q0
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => (q1 ◇ q1) ◇ t) (pe q0 q1))).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))) ◇ t) (cg (fun t => q1 ◇ t) (pe q0 q1))).symm).trans (p6 q1 (((q0 ◇ q0) ◇ q0) ◇ q1) (q1 ◇ q1) q0)).trans (pe q0 q1))
  have pg : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pf q0 q0))).symm).trans ((h q1 ((q0 ◇ q0) ◇ q0) (q0 ◇ q0)).symm)
  have ph : forall (q0 q1:G), (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ t) (pe q0 q1)).symm).trans ((h q1 (((q0 ◇ q0) ◇ q0) ◇ q1) q1).symm)
  have pi : forall (q1 q0 q2:G), (q1 ◇ ((q1 ◇ q1) ◇ q1)) = q1:=by
    intro q1 q0 q2
    exact (((cg (fun t => q1 ◇ t) (p4 q1 ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) q2)).trans (cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (ph q0 q1)))).symm).trans (((cg (fun t => t ◇ ((q2 ◇ q1) ◇ (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ q2))) (ph q0 q1)).symm).trans ((h q1 ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) q2).symm))
  have pj : forall (q1 q0:G), (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) = q1:=by
    intro q1 q0
    exact (((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ q1)) (ph q0 q1))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (ph q0 q1)))))).symm).trans (((cg (fun t => t ◇ (q1 ◇ (q1 ◇ ((((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ q1) ◇ (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ q1))))) (ph q0 q1)).symm).trans (p3 q1 ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1)))
  have pk : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) ((h q0 q0 q0).symm))).symm).trans (pj (q0 ◇ q0) q0)
  have pl : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (p4 q0 (q0 ◇ q0) (q0 ◇ q0)))).trans (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (pk q0)))).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (pk q0))).symm).trans (p8 q0 q0 ((q0 ◇ q0) ◇ q0) q0))
  have pm : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (ph q0 ((q0 ◇ q0) ◇ q0))).symm).trans (((cg (fun t => t ◇ (((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0))) (ph q0 ((q0 ◇ q0) ◇ q0))).symm).trans (pg ((q0 ◇ q0) ◇ q0) ((q0 ◇ q0) ◇ q0)))
  have pn : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ ((q2 ◇ q1) ◇ ((q0 ◇ q2) ◇ ((q2 ◇ q2) ◇ q0)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => (q2 ◇ q1) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q2) ◇ ((q2 ◇ q2) ◇ q0))) (cg (fun t => t ◇ q1) (pi q2 (q2 ◇ ((q2 ◇ q2) ◇ q2)) (q2 ◇ ((q2 ◇ q2) ◇ q2)))))).symm).trans (((cg (fun t => (q2 ◇ q1) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q2) ◇ ((q2 ◇ q2) ◇ q0))) (cg (fun t => t ◇ q1) (cg (fun t => q2 ◇ t) (pm q2))))).symm).trans (pa (q2 ◇ q2) q0 q1 q2))
  have po : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (pk q0))).symm).trans (((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p7 q0 q0 q0 q0))).symm).trans (pn (q0 ◇ q0) q1 q0))
  have pp : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ q2) ◇ ((((q0 ◇ q0) ◇ q1) ◇ q2) ◇ (q0 ◇ q0))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q2) ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q2) ◇ t) (cg (fun t => q0 ◇ t) (pi q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)) (q0 ◇ ((q0 ◇ q0) ◇ q0)))))).symm).trans (((cg (fun t => ((q1 ◇ q0) ◇ q2) ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q2) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (pm q0))))).symm).trans (pb q0 (q0 ◇ q0) q1 q2))
  have pq : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (pf q0 q0))).symm).trans (pe q0 (q0 ◇ q0))
  have pr : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0
    exact ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (pq q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pl (q0 ◇ q0)))).trans (pl (q0 ◇ q0))).symm).trans (((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))) (pq q0)).symm).trans (po ((q0 ◇ q0) ◇ (q0 ◇ q0)) (q0 ◇ (q0 ◇ q0))))
  have ps : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact (((cg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (pr q0)).trans (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (pr q0))).symm).trans ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p4 q0 q0 q0))).symm).trans (pr (q0 ◇ q0))).trans (p5 q0 q0))
  have pt : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ t) (ps q0))).symm).trans ((h q1 (q0 ◇ (q0 ◇ q0)) (q0 ◇ (q0 ◇ q0))).symm)
  have pu : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0))) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (pn q0 (q1 ◇ q1) q1))).trans (pk q1)).symm).trans (((cg (fun t => t ◇ (((q1 ◇ (q1 ◇ q1)) ◇ ((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0)))) ◇ q1)) (pn q0 (q1 ◇ q1) q1)).symm).trans (pt q1 ((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0)))))).symm
  have pv : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => ((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0))) ◇ t) (ps q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (pu q0 q1)))).trans (pk q1)).symm).trans (((cg (fun t => t ◇ (((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0))) ◇ ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q1 ◇ q1))))) (pu q0 q1)).symm).trans (po (q1 ◇ (q1 ◇ q1)) ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0))))).symm
  have pw : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1)))) = ((q1 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) (pv q0 q1))).symm).trans (((cg (fun t => t ◇ (((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0)) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1)))) (pv q0 q1)).symm).trans (po (q0 ◇ q1) ((q1 ◇ q1) ◇ q0)))
  have px : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) = q0:=by
    intro q0 q1
    exact (((((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (pw q0 q1))).trans (cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (p4 q0 (q1 ◇ q1) (q1 ◇ q1)))).trans (p5 q0 (q1 ◇ q1))).symm).trans (((cg (fun t => t ◇ (((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1)))) ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1)))) (pw q0 q1)).symm).trans (po (q1 ◇ q1) ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1)))))).symm
  have py : forall (q0 q1 q2:G), (((((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q1) ◇ q2) ◇ ((q0 ◇ q2) ◇ (q1 ◇ q1))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q1) ◇ q2) ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ q2) (px q0 q1)))).symm).trans (pp q1 ((q0 ◇ q1) ◇ (q0 ◇ q1)) q2)
  have pz : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q1))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => q0 ◇ t) (px q0 q1)))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1)))) ◇ (q1 ◇ q1))) (pv ((q0 ◇ q1) ◇ (q0 ◇ q1)) q1)).symm).trans (py q0 q1 ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))))).trans (px q0 q1))
  have p10 : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q1) ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (ps q0))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))) (ps q0)).symm).trans (pz q1 (q0 ◇ (q0 ◇ q0))))
  exact (p10 (y ◇ z) x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19010_to_19238 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19010_to_19238
