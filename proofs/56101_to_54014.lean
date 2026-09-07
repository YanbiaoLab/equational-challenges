-- Equation56101 → Equation54014
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = (x ◇ z) ◇ (x ◇ y)
-- Conclusion: x ◇ (y ◇ x) = x ◇ (x ◇ (y ◇ y))
-- Original submission SHA-256: 3fc8b4b3ff01a9de3c0983acc81aea1e3dd3055fb80c609e41ced84bc772015c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (x ◇ z) ◇ (x ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = x ◇ (x ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1 q2 q3:G), ((q0 ◇ (q1 ◇ q2)) ◇ ((q0 ◇ q2) ◇ q3)) = ((q0 ◇ q2) ◇ (q3 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q0 ◇ q2) ◇ q3)) ((h q0 q1 q2).symm)).symm).trans ((h (q0 ◇ q2) q3 (q0 ◇ q1)).symm)
  have p1 : forall (q0 q1 q2 q3:G), (((q0 ◇ q2) ◇ q3) ◇ (q0 ◇ (q1 ◇ q2))) = ((q0 ◇ q2) ◇ ((q0 ◇ q1) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q0 ◇ q2) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q0 ◇ q2) (q0 ◇ q1) q3).symm)
  have p2 : forall (q0 q1 q2 q3:G), ((q1 ◇ q3) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q2))) = ((q1 ◇ (q2 ◇ q3)) ◇ (q1 ◇ (q0 ◇ q3))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q1 ◇ (q2 ◇ q3)) ◇ t) ((h q1 q0 q3).symm)).symm).trans (p0 q1 q2 q3 (q1 ◇ q0))).symm
  have p3 : forall (q0 q1 q2 q3:G), ((q1 ◇ (q2 ◇ q3)) ◇ (q1 ◇ (q0 ◇ q3))) = ((q1 ◇ q3) ◇ (q1 ◇ (q2 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q1 ◇ q3) ◇ t) ((h q1 q2 q0).symm)).symm).trans (p2 q0 q1 q2 q3)).symm
  have p4 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q2))) = ((q3 ◇ q2) ◇ (q3 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (((p3 q0 q3 q1 q2).symm).trans ((h q3 (q0 ◇ q2) (q1 ◇ q2)).symm)).symm
  have p5 : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q2 ◇ (q0 ◇ q0))) = (q2 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h q0 q1 q1).symm)).symm).trans (p4 q0 q0 q1 q2)).symm
  have p6 : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ (q2 ◇ q2))) = (q1 ◇ ((q0 ◇ q0) ◇ q2)):=by
    intro q0 q1 q2
    exact ((p5 q0 q2 q1).symm).trans ((h q1 (q0 ◇ q0) q2).symm)
  have p7 : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ ((q2 ◇ q2) ◇ q0)) = (q2 ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact ((p6 q2 (q2 ◇ q1) q0).symm).trans ((p5 q0 q1 q2).trans (p6 q0 q2 q1))
  have p8 : forall (q0 q1 q2 q3:G), ((q1 ◇ q3) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q2))) = ((q1 ◇ q3) ◇ (q1 ◇ (q2 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (p2 q0 q1 q2 q3).trans (p3 q0 q1 q2 q3)
  have p9 : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ ((q0 ◇ q0) ◇ q1))) = (q3 ◇ ((q2 ◇ q2) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (p6 q0 q2 q1)).symm).trans (((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) ((h q0 q1 q1).symm))).symm).trans (p6 q2 q3 (q0 ◇ q1)))
  have pa : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ q2) ◇ (q0 ◇ q1))) = ((q1 ◇ q1) ◇ (q2 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact ((p7 q2 (q0 ◇ q1) q1).symm).trans (p0 q1 q0 q1 q2)
  have pb : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ ((q3 ◇ q3) ◇ (q0 ◇ q1))) = (q3 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q2))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q3 ◇ q2) ◇ t) (p6 q0 q3 q1)).trans (p9 q0 q1 q3 (q3 ◇ q2))).symm).trans (((cg (fun t => (q3 ◇ q2) ◇ t) (cg (fun t => q3 ◇ t) ((h q0 q1 q1).symm))).symm).trans (p5 (q0 ◇ q1) q2 q3))
  have pc : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ q2) ◇ ((q0 ◇ q0) ◇ q1)) = ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact ((p6 q0 ((q0 ◇ q1) ◇ q2) q1).symm).trans (p1 q0 q1 q1 q2)
  have pd : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q1) ◇ q0)) = ((q0 ◇ q0) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((p7 q1 q0 q0).symm).trans (((pc q0 q0 q1).symm).trans ((h (q0 ◇ q0) q0 q1).symm))
  have pe : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))) = ((q2 ◇ q1) ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) (pd q1 q0)).symm).trans (p9 q0 q1 q1 q2)).trans (p4 q1 q0 q1 q2)
  have pf : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q2 ◇ (q0 ◇ q1))) = (q2 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h q1 q0 q1).symm)).symm).trans (pe q0 q1 q2)).symm
  have pg : forall (q0 q1 q2:G), (q1 ◇ ((q0 ◇ q2) ◇ q2)) = (q1 ◇ (q2 ◇ (q0 ◇ q2))):=by
    intro q0 q1 q2
    exact (((pf q0 q2 q1).symm).trans ((h q1 (q0 ◇ q2) q2).symm)).symm
  have ph : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))) = (q2 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (pe q0 q1 q2).trans (pf q0 q1 q2)
  have pi : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ (q1 ◇ q1)) ◇ q2)) = ((q2 ◇ q2) ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q2) ((h q0 q1 q1).symm))).symm).trans (pd q2 (q0 ◇ q1))
  have pj : forall (q0 q1 q2 q3:G), ((q2 ◇ ((q0 ◇ q0) ◇ q1)) ◇ (q2 ◇ q3)) = (q2 ◇ ((q3 ◇ q3) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ (q2 ◇ q3)) (p6 q0 q2 q1)).symm).trans ((h q2 q3 (q0 ◇ (q1 ◇ q1))).symm)).trans ((cg (fun t => q2 ◇ t) (p6 q0 q3 q1)).trans (p9 q0 q1 q3 q2))
  have pk : forall (q0 q1 q2 q3:G), (q2 ◇ ((q0 ◇ (q1 ◇ q1)) ◇ q3)) = (q2 ◇ ((q0 ◇ q1) ◇ (q3 ◇ q3))):=by
    intro q0 q1 q2 q3
    exact ((((p9 q0 q1 q2 (q2 ◇ q3)).trans (pb q0 q1 q3 q2)).symm).trans (((cg (fun t => (q2 ◇ q3) ◇ t) (p6 q0 q2 q1)).symm).trans ((h q2 (q0 ◇ (q1 ◇ q1)) q3).symm))).symm
  have pl : forall (q0 q1 q2 q3:G), ((q2 ◇ q2) ◇ (q2 ◇ (q0 ◇ q1))) = (q2 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q2))):=by
    intro q0 q1 q2 q3
    exact (((pk q0 q1 q2 q2).symm).trans (pi q0 q1 q2)).symm
  have pm : forall (q0 q1 q2 q3:G), (q2 ◇ (((q0 ◇ q0) ◇ q1) ◇ q3)) = (q2 ◇ ((q0 ◇ q1) ◇ (q3 ◇ q3))):=by
    intro q0 q1 q2 q3
    exact (((pb q0 q1 q3 q2).symm).trans (((p9 q0 q1 q2 (q2 ◇ q3)).symm).trans ((h q2 ((q0 ◇ q0) ◇ q1) q3).symm))).symm
  have pn : forall (q0 q1:G), ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) = ((q0 ◇ q0) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((pa q0 q0 q1).trans (p6 q1 (q0 ◇ q0) q0)).symm).trans ((((pl q1 q1 q0 q0).symm).trans (p6 q0 (q0 ◇ q0) q1)).trans ((p7 q1 q0 q0).trans (pd q0 q1)))
  have po : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)) = ((q1 ◇ q1) ◇ (q2 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q1 ◇ q2)) (pd q1 q0)).symm).trans (pj q0 q1 q1 q2)).trans (pa q0 q1 q2)
  have pp : forall (q0 q1 q2:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q1 ◇ q2)) = ((q1 ◇ q1) ◇ (q2 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q1 ◇ q2)) ((h q1 q0 q1).symm)).symm).trans (po q0 q1 q2)
  have pq : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q2 ◇ (q1 ◇ q0))) = (q1 ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact ((pp q0 q1 q2).symm).trans ((h q1 q2 (q0 ◇ q1)).symm)
  have pr : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q2) ◇ (q3 ◇ (q1 ◇ q0))) ◇ (q3 ◇ q4)) = (q3 ◇ ((q4 ◇ q2) ◇ (q4 ◇ (q1 ◇ q0)))):=by
    intro q0 q1 q2 q3 q4
    exact (((cg (fun t => t ◇ (q3 ◇ q4)) (p4 q0 q1 q2 q3)).symm).trans ((h q3 q4 ((q0 ◇ q2) ◇ (q1 ◇ q2))).symm)).trans (cg (fun t => q3 ◇ t) (p4 q0 q1 q2 q4))
  have ps : forall (q0 q1 q2 q3 q4:G), (q3 ◇ ((q4 ◇ q2) ◇ (q4 ◇ (q1 ◇ q0)))) = ((q3 ◇ ((q1 ◇ q0) ◇ q2)) ◇ (q3 ◇ q4)):=by
    intro q0 q1 q2 q3 q4
    exact (((cg (fun t => t ◇ (q3 ◇ q4)) ((h q3 (q1 ◇ q0) q2).symm)).symm).trans (pr q0 q1 q2 q3 q4)).symm
  have pt : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ ((q1 ◇ q0) ◇ q2)) ◇ (q3 ◇ q4)) = (q3 ◇ (q4 ◇ ((q1 ◇ q0) ◇ q2))):=by
    intro q0 q1 q2 q3 q4
    exact (((cg (fun t => q3 ◇ t) ((h q4 (q1 ◇ q0) q2).symm)).symm).trans (ps q0 q1 q2 q3 q4)).symm
  have pu : forall (q0 q1 q2 q3 q4:G), (q3 ◇ ((q4 ◇ q2) ◇ (q4 ◇ (q1 ◇ q0)))) = (q3 ◇ (q4 ◇ ((q1 ◇ q0) ◇ q2))):=by
    intro q0 q1 q2 q3 q4
    exact (ps q0 q1 q2 q3 q4).trans (pt q0 q1 q2 q3 q4)
  have pv : forall (q0 q1 q2 q3 q4:G), (q3 ◇ (((q0 ◇ q2) ◇ (q1 ◇ q2)) ◇ q4)) = ((q3 ◇ q4) ◇ (q3 ◇ ((q1 ◇ q0) ◇ q2))):=by
    intro q0 q1 q2 q3 q4
    exact (((p8 q2 q3 (q1 ◇ q0) q4).symm).trans (((cg (fun t => (q3 ◇ q4) ◇ t) (p4 q0 q1 q2 q3)).symm).trans ((h q3 ((q0 ◇ q2) ◇ (q1 ◇ q2)) q4).symm))).symm
  have pw : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q1 ◇ (q2 ◇ q0))) = (q1 ◇ (q2 ◇ (q0 ◇ q2))):=by
    intro q0 q1 q2
    exact ((p4 q0 q2 q2 q1).symm).trans ((((pm q0 q2 q1 q2).symm).trans (pg (q0 ◇ q0) q1 q2)).trans ((cg (fun t => q1 ◇ t) (pd q2 q0)).trans (ph q0 q2 q1)))
  have px : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ q0) ◇ q2)) = (q1 ◇ (q2 ◇ (q0 ◇ q2))):=by
    intro q0 q1 q2
    exact (((pw q0 q1 q2).symm).trans ((h q1 (q2 ◇ q0) q2).symm)).symm
  have py : forall (q0 q1 q2 q3:G), (((q0 ◇ q1) ◇ q3) ◇ ((q0 ◇ q1) ◇ (q2 ◇ q2))) = ((q0 ◇ q1) ◇ ((q2 ◇ q2) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((pk q0 q1 ((q0 ◇ q1) ◇ q3) q2).symm).trans (((cg (fun t => ((q0 ◇ q1) ◇ q3) ◇ t) (cg (fun t => t ◇ q2) ((h q0 q1 q1).symm))).symm).trans (p7 q2 q3 (q0 ◇ q1)))
  have pz : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ q2) ◇ (q1 ◇ (q0 ◇ q1))) = ((q1 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((px q0 ((q1 ◇ q0) ◇ q2) q1).symm).trans ((h (q1 ◇ q0) q1 q2).symm)
  have p10 : forall (q0 q1 q2 q3:G), (((q1 ◇ q2) ◇ q3) ◇ ((q1 ◇ q1) ◇ (q0 ◇ q2))) = ((q1 ◇ q2) ◇ ((q1 ◇ q0) ◇ (q3 ◇ q3))):=by
    intro q0 q1 q2 q3
    exact (((p9 q0 q2 q1 ((q1 ◇ q2) ◇ q3)).symm).trans (p1 q1 (q0 ◇ q0) q2 q3)).trans (pk q1 q0 (q1 ◇ q2) q3)
  have p11 : forall (q0 q1 q2:G), (q0 ◇ ((q2 ◇ q2) ◇ (q1 ◇ q1))) = ((q0 ◇ q1) ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2
    exact (((pz q1 q0 q2).symm).trans ((((cg (fun t => ((q0 ◇ q1) ◇ q2) ◇ t) ((h q0 q1 q0).symm)).symm).trans (p10 q0 q0 q1 q2)).trans (pb q2 q2 q1 q0))).symm
  have p12 : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q1) ◇ q0)) = ((q2 ◇ q0) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact ((((p4 q1 q1 q0 q2).trans (p6 q2 (q2 ◇ q0) q1)).trans (p7 q1 q0 q2)).symm).trans ((((cg (fun t => q2 ◇ t) (p11 q1 q0 q0)).symm).trans (p6 q1 q2 (q0 ◇ q0))).trans (p11 q2 q0 q1))
  have p13 : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ (q2 ◇ q2))) = ((q1 ◇ q2) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (p6 q0 q1 q2).trans (p12 q2 q0 q1)
  have p14 : forall (q0 q1 q2:G), ((q2 ◇ (q1 ◇ q0)) ◇ (q2 ◇ q1)) = (q2 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact ((p12 (q1 ◇ q0) q1 q2).symm).trans (ph q0 q1 q2)
  have p15 : forall (q0 q1 q2 q3:G), ((q0 ◇ q2) ◇ ((q3 ◇ q3) ◇ (q0 ◇ q1))) = ((q0 ◇ q2) ◇ ((q3 ◇ q1) ◇ (q3 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact ((p0 q0 q1 q2 (q3 ◇ q3)).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q2) ◇ (q3 ◇ q3))) ((h q0 q1 q2).symm)).symm).trans (p5 q3 (q0 ◇ q1) (q0 ◇ q2))).trans (((cg (fun t => (q0 ◇ q2) ◇ t) (p4 q0 q0 q1 q3)).trans (pu q0 q0 q1 (q0 ◇ q2) q3)).trans (cg (fun t => (q0 ◇ q2) ◇ t) (p12 q1 q0 q3))))
  have p16 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ (q2 ◇ q0))) = (q1 ◇ (q2 ◇ (q0 ◇ q2))):=by
    intro q0 q1 q2
    exact (((p14 q0 q2 q1).symm).trans ((h q1 q2 (q2 ◇ q0)).symm)).symm
  have p17 : forall (q0 q1 q2:G), ((q0 ◇ q2) ◇ (q0 ◇ (q1 ◇ q0))) = ((q0 ◇ q2) ◇ (q0 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q0 ◇ q2) ◇ t) ((h q0 q1 q0).symm)).symm).trans (p15 q0 q1 q2 q0)).trans (p8 q1 q0 q0 q2)
  have p18 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q1 ◇ (q0 ◇ q1))) = (q1 ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact ((p16 q0 (q1 ◇ q2) q1).symm).trans (((p17 q1 q0 q2).symm).trans ((h q1 (q0 ◇ q1) q2).symm))
  have p19 : forall (q0 q1 q2:G), ((q0 ◇ q2) ◇ (q0 ◇ (q0 ◇ q1))) = (q0 ◇ ((q1 ◇ q0) ◇ q2)):=by
    intro q0 q1 q2
    exact (((p18 q1 q0 q2).symm).trans (p17 q0 q1 q2)).symm
  have p1a : forall (q0 q1 q2:G), (q1 ◇ ((q1 ◇ q0) ◇ q2)) = (q1 ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact (((p19 q1 q0 q2).symm).trans ((h q1 (q1 ◇ q0) q2).symm)).symm
  have p1b : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q0))) = (q2 ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h q2 q0 q1).symm)).symm).trans (p1a q1 q2 (q2 ◇ q0))).symm
  have p1c : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q1 ◇ (q0 ◇ q0))) = ((q1 ◇ q2) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((((p11 q1 q2 q0).symm).trans (p6 (q0 ◇ q0) q1 q2)).trans (((pv q0 q0 q0 q1 q2).trans (cg (fun t => (q1 ◇ q2) ◇ t) (p12 q0 q0 q1))).trans (p8 q0 q1 q0 q2))).symm
  have p1d : forall (q0 q1 q2 q3:G), (q3 ◇ ((q2 ◇ q1) ◇ (q2 ◇ q0))) = ((q3 ◇ (q0 ◇ q1)) ◇ (q3 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (p12 q1 q0 q2)).symm).trans ((p9 q0 q1 q2 q3).trans (p12 (q0 ◇ q1) q2 q3))
  have p1e : forall (q0 q1 q2 q3:G), ((q3 ◇ (q0 ◇ q1)) ◇ (q3 ◇ q2)) = (q3 ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => q3 ◇ t) ((h q2 q0 q1).symm)).symm).trans (p1d q0 q1 q2 q3)).symm
  have p1f : forall (q0 q1 q2 q3:G), (q3 ◇ ((q2 ◇ q1) ◇ (q2 ◇ q0))) = (q3 ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q3
    exact (p1d q0 q1 q2 q3).trans (p1e q0 q1 q2 q3)
  have p1g : forall (q0 q1:G), (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q1)) = ((q0 ◇ q0) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((p12 q0 q1 (q0 ◇ q0)).symm).trans (pn q0 q1)
  have p1h : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ q0)) = ((q1 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((p1g q1 q0).symm).trans ((h (q1 ◇ q1) q0 q1).symm)
  have p1i : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((p1h q0 q1).symm).trans ((h q1 q0 q1).symm)
  have p1j : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ q0)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (p1h q0 q1).trans (p1i q0 q1)
  have p1k : forall (q0 q1 q2 q3:G), (((q0 ◇ q1) ◇ q3) ◇ ((q0 ◇ q1) ◇ q2)) = ((q0 ◇ q1) ◇ ((q2 ◇ q2) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((p1c q2 (q0 ◇ q1) q3).symm).trans (py q0 q1 q2 q3)
  have p1l : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ ((q2 ◇ q2) ◇ q3)) = ((q0 ◇ q1) ◇ (q2 ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((p1k q0 q1 q2 q3).symm).trans ((h (q0 ◇ q1) q2 q3).symm)
  have p1m : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ q2) ◇ (q0 ◇ q1)) = ((q0 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((p1l (q0 ◇ q0) q2 q0 q1).symm).trans ((h (q0 ◇ q0) q1 q2).symm)
  have p1n : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q2 ◇ (q0 ◇ q1))) = (q1 ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact (((p1e q0 q1 q2 q1).symm).trans (((cg (fun t => t ◇ (q1 ◇ q2)) (p1i q0 q1)).symm).trans (p1m q1 q2 (q0 ◇ q1)))).symm
  have p1o : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q2 ◇ q0))) = (q2 ◇ (q1 ◇ (q0 ◇ q2))):=by
    intro q0 q1 q2
    exact (((pq q0 q2 q1).symm).trans ((((cg (fun t => (q2 ◇ q2) ◇ t) ((h q1 q2 q0).symm)).symm).trans (p1n q1 q2 (q1 ◇ q0))).trans (p1f q2 q0 q1 q2))).symm
  have p1p : forall (q0 q1 q2:G), (q2 ◇ (q2 ◇ (q0 ◇ q1))) = (q2 ◇ ((q0 ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact ((((p4 q1 q0 q2 q2).trans (p1j (q0 ◇ q1) q2)).symm).trans (((p1o q0 (q1 ◇ q2) q2).symm).trans (p1b q0 q1 q2))).symm
  have p1q : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q0)) = (q0 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((((p12 q0 q1 q0).trans (p1j q1 q0)).symm).trans (((p1p q1 q1 q0).symm).trans (p13 q0 q0 q1))).symm
  exact (calc
    (x ◇ (y ◇ x)) = (x ◇ (y ◇ x)):=rfl
    _ = (x ◇ (x ◇ (y ◇ y))):=((p13 x x y).trans (p1q x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56101_to_54014 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56101_to_54014
