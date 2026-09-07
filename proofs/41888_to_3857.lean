-- Equation41888 → Equation3857
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (x ◇ (y ◇ z)))
-- Conclusion: x ◇ y = (z ◇ w) ◇ (u ◇ y)
-- Original submission SHA-256: dd727c6546bf1737c1e4891b2e18d2127dba61f007494f1da25b5238ecadeb6d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (x ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ (u ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) ((h q0 q0 q0).symm)).symm).trans ((h q0 q0 (q0 ◇ q0)).symm)
  have p1 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q1 ◇ q0))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) ((h q1 q0 q0).symm))).symm).trans ((h q0 q1 (q1 ◇ (q0 ◇ q0))).symm)
  have p2 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q2)))) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) ((h q0 q2 q0).symm)))).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ (q2 ◇ q0)))).symm)
  have p3 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ q1)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) ((h q1 q1 q0).symm)).symm).trans (p2 q1 q1 (q1 ◇ q0))
  have p4 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) (p2 q0 q1 q1)).symm).trans (p2 q1 q1 (q0 ◇ q1))
  have p5 : forall (q0 q1:G), (q0 ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (p0 (q0 ◇ q1))).symm).trans ((h (q0 ◇ q1) q0 q1).symm)
  have p6 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ (q0 ◇ q1))) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (p1 q0 q1))).symm).trans (p2 q0 q1 (q1 ◇ q0))
  have p7 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ (q1 ◇ q0))) = (q1 ◇ (q1 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (((((cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) (p3 q1 q1)).trans (cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) (p0 q1))).trans (p3 (q1 ◇ q0) q1)).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (p3 q0 q1)).symm).trans (p4 (q1 ◇ q0) (q1 ◇ q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (p3 q0 q1)))).symm
  have p8 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ q0)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((((cg (fun t => (q1 ◇ q0) ◇ t) (p7 (q1 ◇ q0) q1)).trans (p2 q1 q1 (q1 ◇ q0))).symm).trans (((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p7 q0 q1))).symm).trans (p2 q1 (q1 ◇ q1) (q1 ◇ q0)))).symm
  have p9 : forall (q0 q1:G), ((q0 ◇ q0) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (p8 (q0 ◇ q1) q0)).trans (p2 q0 q0 q1)).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p8 q1 q0))).symm).trans (p2 q0 (q0 ◇ q0) q1))).symm
  have pa : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (p9 q0 q1))).trans (p1 q1 q0)).symm).trans (((p9 q0 (q1 ◇ ((q0 ◇ q0) ◇ q1))).symm).trans (p1 q1 (q0 ◇ q0)))).symm
  have pb : forall (q0 q1:G), ((q0 ◇ q1) ◇ q0) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q1)) (p9 q0 q1))).trans (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p9 q0 q1)))).trans (pa (q0 ◇ q1) q0)).symm).trans ((((p9 q0 (((q0 ◇ q0) ◇ q1) ◇ ((q0 ◇ q0) ◇ q1))).symm).trans (p5 (q0 ◇ q0) q1)).trans ((cg (fun t => t ◇ (q0 ◇ q0)) (p9 q0 q1)).trans (pa q0 (q0 ◇ q1))))).symm
  have pc : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ q1))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (pa q1 q0))).symm).trans ((h q0 q1 q1).symm)
  have pd : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ q1) = (q1 ◇ ((q0 ◇ q1) ◇ q1)):=by
    intro q0 q1
    exact ((((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p9 q1 (q1 ◇ q1))).trans (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (pa q1 q1))).trans (pa q1 (q1 ◇ (q0 ◇ q1)))).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (p4 q0 q1)).symm).trans (p4 (q0 ◇ q1) (q1 ◇ q1))).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (pa q1 (q0 ◇ q1))).trans (p9 q1 ((q0 ◇ q1) ◇ q1))))
  have pe : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (p6 (q0 ◇ q1) q1)).trans (p2 q0 q1 q1)).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (pd q0 q1))).symm).trans (pc (q1 ◇ (q0 ◇ q1)) q1))).symm
  have pf : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((pe q0 q1).symm).trans (pd q0 q1)).symm
  have pg : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q0 ◇ q1))) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (pa q1 q1)).trans (pa q1 (q1 ◇ (q0 ◇ q1)))).trans (pe q0 q1)).symm).trans (((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => q1 ◇ t) (pe q0 q1))).symm).trans (p1 q1 (q1 ◇ (q0 ◇ q1))))).symm
  have ph : forall (q0 q1:G), (q1 ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((pa q1 q0).symm).trans (((cg (fun t => q0 ◇ t) (pg q0 q1)).symm).trans ((h q1 q0 q1).symm))).symm
  have pi : forall (q0 q1:G), (((q0 ◇ q1) ◇ q0) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (ph (q0 ◇ q0) q1))).trans (cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (p9 q0 q1)))).trans (cg (fun t => q1 ◇ t) (ph (q0 ◇ q1) q0))).trans (ph ((q0 ◇ q1) ◇ q0) q1)).symm).trans ((((cg (fun t => q1 ◇ t) (p9 q0 (q1 ◇ (q0 ◇ q0)))).symm).trans (p1 (q0 ◇ q0) q1)).trans (p9 q0 q1))
  have pj : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (ph (q0 ◇ q0) q1))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (p9 q0 q1)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (ph (q0 ◇ q1) q1))).trans (p9 q0 ((q0 ◇ q1) ◇ q1))).trans (ph ((q0 ◇ q1) ◇ q1) q0)).symm).trans ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p0 q0)))).symm).trans (p2 q0 q1 (q0 ◇ q0))).trans ((ph (q0 ◇ q0) q1).trans (p9 q0 q1)))
  have pk : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) = (((q0 ◇ q1) ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => q1 ◇ t) (ph q0 q1))).trans (cg (fun t => t ◇ (q1 ◇ q1)) (ph (q0 ◇ q1) q1))).symm).trans ((((cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) ((h q1 q1 q0).symm)).symm).trans (pc q1 (q1 ◇ (q1 ◇ q0)))).trans (((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (ph q0 q1))).trans (cg (fun t => q1 ◇ t) (ph (q0 ◇ q1) q1))).trans (ph ((q0 ◇ q1) ◇ q1) q1)))
  have pl : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q1) ◇ q1) ◇ q1) = (((q0 ◇ q1) ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) (pk q0 q1)).trans (ph (((q0 ◇ q1) ◇ q1) ◇ q1) q1)).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) (pf q0 q1))).symm).trans (p1 ((q0 ◇ q1) ◇ q1) q1))
  have pm : forall (q0 q1 q2:G), ((((q0 ◇ q2) ◇ q1) ◇ q1) ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact (((((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p9 q0 q2)))).trans (cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (ph (q0 ◇ q2) q1)))).trans (cg (fun t => q0 ◇ t) (ph ((q0 ◇ q2) ◇ q1) q1))).trans (ph (((q0 ◇ q2) ◇ q1) ◇ q1) q0)).symm).trans ((((p9 q0 (q1 ◇ (q1 ◇ ((q0 ◇ q0) ◇ q2)))).symm).trans ((h q1 (q0 ◇ q0) q2).symm)).trans ((ph (q0 ◇ q0) q1).trans (p9 q0 q1)))
  have pn : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((p9 q1 q1).symm).trans ((((pm (q1 ◇ q1) q1 q0).symm).trans (pk ((q1 ◇ q1) ◇ q0) q1)).trans (((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (p9 q1 q0)))).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (ph q0 q1))))).trans (pl q0 q1)))).symm
  have po : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => q0 ◇ t) (ph q0 q1)))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (ph (q0 ◇ q1) q0)))).trans (ph (((q0 ◇ q1) ◇ q0) ◇ (q0 ◇ q1)) q1)).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q1 ◇ q0)) ◇ t) (p1 q0 q1))).symm).trans (p1 (q0 ◇ (q1 ◇ q0)) q1)).trans (((cg (fun t => t ◇ q1) (cg (fun t => q0 ◇ t) (ph q0 q1))).trans (cg (fun t => t ◇ q1) (ph (q0 ◇ q1) q0))).trans (pi q0 q1)))
  have pp : forall (q0 q1:G), ((q0 ◇ q1) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ q1) (cg (fun t => ((q0 ◇ q1) ◇ (((q0 ◇ q1) ◇ q0) ◇ (q0 ◇ q1))) ◇ t) (po q0 q1))).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q0 ◇ q1)) (ph (((q0 ◇ q1) ◇ q0) ◇ (q0 ◇ q1)) (q0 ◇ q1))))).trans (cg (fun t => t ◇ q1) (pm (q0 ◇ q1) (q0 ◇ q1) q0))).trans (p9 (q0 ◇ q1) q1)).symm).trans ((((cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((((q0 ◇ q1) ◇ q0) ◇ (q0 ◇ q1)) ◇ q1)) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ q0) ◇ (q0 ◇ q1))) (po q0 q1)))).symm).trans (po (((q0 ◇ q1) ◇ q0) ◇ (q0 ◇ q1)) q1)).trans (po q0 q1))
  have pq : forall (q0 q1:G), ((q0 ◇ q1) ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q0) (pp q0 q1)).symm).trans (pj q0 q1)
  have pr : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q1) (pp q0 q1)).trans (pp q0 q1)).symm).trans (pn q0 q1)).symm
  have ps : forall (q0 q1:G), (q0 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((pr (q0 ◇ q1) q0).trans (pq q0 q1)).symm
  have pt : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((ps q0 q2).symm).trans ((((pr q0 q2).symm).trans (pr q1 q2)).trans (ps q1 q2))).symm
  have pu : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (ps q1 (q1 ◇ q0)))).trans (cg (fun t => (q1 ◇ q0) ◇ t) (ps q1 (q1 ◇ q1)))).trans (ps (q1 ◇ q0) (q1 ◇ q1))).symm).trans ((((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (pb q1 q0))).symm).trans (p1 q1 (q1 ◇ q0))).trans (ps q1 (q1 ◇ q0)))
  have pv : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((((((((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (ps q1 (q1 ◇ q0)))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q1))) (ps q0 q1))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (ps (q1 ◇ q0) (q1 ◇ q1)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pu q0 q1))).trans (ps (q0 ◇ q0) (q1 ◇ q1))).trans (pu q0 q0)).symm).trans ((((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (p6 q0 q1))).symm).trans (p2 q1 (q1 ◇ q0) (q0 ◇ q1))).trans (cg (fun t => (q1 ◇ q0) ◇ t) (ps q0 q1)))).symm
  have pw : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q2 ◇ q1) ◇ t) (pt q0 q1 q0)).symm).trans (pv q1 q2)
  have px : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ q2) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((((cg (fun t => q2 ◇ t) (pw q0 q0 q1)).trans (ps q2 (q0 ◇ q0))).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (pw q2 q0 q1))).symm).trans ((h (q1 ◇ q0) q2 q2).symm))).symm
  exact (calc
    (x ◇ y) = (x ◇ x):=ps x y
    _ = ((u ◇ y) ◇ (u ◇ y)):=pt (u ◇ y) x u
    _ = ((z ◇ w) ◇ (u ◇ y)):=(px w z (u ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41888_to_3857 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41888_to_3857
