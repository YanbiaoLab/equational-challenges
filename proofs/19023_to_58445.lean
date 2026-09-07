-- Equation19023 → Equation58445
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
-- Conclusion: (x ◇ y) ◇ x = y ◇ (y ◇ (y ◇ x))
-- Original submission SHA-256: 87898c1862e6c3f2eb2e3bb4a7b8541f5330029511de6006e29935eda41d5213
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ y) ◇ x = y ◇ (y ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) ((h b (b ◇ a) a).symm)).symm).trans ((h (a ◇ (b ◇ a)) b (b ◇ a)).symm)
  have p1:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => (a ◇ a) ◇ t) ((h a a a).symm))).symm).trans (p0 (a ◇ a) (a ◇ a))
  have p2:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a a a)
  have p3:=fun (a:G)=>by
    exact ((p2 a a a).symm).trans ((h a a a).symm)
  have p4:=fun (a:G)=>by
    exact (p1 a).trans (p3 a)
  have p5:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((d ◇ (b ◇ a)) ◇ (((c ◇ b) ◇ (a ◇ c)) ◇ d))) ((h a b c).symm)).symm).trans ((h ((c ◇ b) ◇ (a ◇ c)) (b ◇ a) d).symm)
  have p6:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p4 a)))).symm).trans (p0 (a ◇ a) ((a ◇ a) ◇ a))).trans (cg (fun t => (a ◇ a) ◇ t) (p4 a))
  have p7:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p0 a b)))).symm).trans (p0 b (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => b ◇ t) (p0 a b))
  have p8:=fun (a b c d:G)=>by
    exact ((cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ d) ◇ t) (cg (fun t => t ◇ (d ◇ (b ◇ a))) ((h a b c).symm))).symm).trans ((h d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a)).symm)
  have p9:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p6 a)))).symm).trans (p0 ((a ◇ a) ◇ a) (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))).trans (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p6 a))
  have pa:=fun (a:G)=>by
    exact (((p3 ((a ◇ a) ◇ a)).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))) (p9 a)).symm).trans (p4 (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))))).symm
  have pb:=fun (a b c d:G)=>by
    exact ((cg (fun t => (d ◇ (b ◇ a)) ◇ t) (cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ d) ◇ t) ((h a b c).symm))).symm).trans ((h (b ◇ a) d ((c ◇ b) ◇ (a ◇ c))).symm)
  have pc:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p7 a b)).symm).trans ((((cg (fun t => t ◇ (((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ (a ◇ (b ◇ a))))) (p7 a b)).symm).trans (pa (b ◇ (a ◇ (b ◇ a))))).trans (p7 a b))
  have pd:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p4 a))).symm).trans ((h b (a ◇ a) ((a ◇ a) ◇ a)).symm)
  have pe:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pa a))).symm).trans (pd a ((a ◇ a) ◇ a))
  have pf:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ c))) (p0 a b)).symm).trans ((h b (b ◇ (a ◇ (b ◇ a))) c).symm)
  have pg:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ b))) (p4 a)).symm).trans ((h (a ◇ a) ((a ◇ a) ◇ a) b).symm)
  have ph:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (pa a))).symm).trans (pg a ((a ◇ a) ◇ a))
  have pi:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (pa a))).symm).trans ((h b ((a ◇ a) ◇ a) ((a ◇ a) ◇ a)).symm)
  have pj:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ (b ◇ a))))) (pc a b))).symm).trans (pf a b (b ◇ (a ◇ (b ◇ a))))
  have pk:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (c ◇ (a ◇ (c ◇ a)))) ◇ t) (cg (fun t => (c ◇ b) ◇ t) (p0 a c))).symm).trans ((h (c ◇ (a ◇ (c ◇ a))) b c).symm)
  have pl:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p4 a))).symm).trans ((h ((a ◇ a) ◇ a) b (a ◇ a)).symm)
  have pm:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p3 a))).symm).trans (pl a ((a ◇ a) ◇ (a ◇ a)))
  have pn:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)) (pa a)).symm).trans (pl a ((a ◇ a) ◇ a))
  have po:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a)))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ t) (pa a)))).trans (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (pa a))).symm).trans ((((cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pl a ((a ◇ a) ◇ a)))).symm).trans (pl ((a ◇ a) ◇ a) (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a))).trans ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a)).trans (pa a)))
  have pp:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a)))) (p3 (a ◇ a))).symm).trans (p8 a a a (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))))
  have pq:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (pa a))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (po a))).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (po a)))).symm).trans (p0 ((a ◇ a) ◇ a) ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)))).trans ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (po a)).trans (pa a)))
  have pr:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pn a)).trans (pa a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)) ◇ t) (pq a)).symm).trans (pi a (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)))).symm
  have ps:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (pe a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pr a)))).symm).trans (p0 a ((a ◇ a) ◇ ((a ◇ a) ◇ a)))).trans (cg (fun t => a ◇ t) (pr a)))
  have pt:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (ps a)).symm).trans (ph a)
  have pu:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ (a ◇ (a ◇ a))))) (pr a)).symm).trans (p8 (a ◇ a) a a a)
  have pv:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ t) (pt b)).symm).trans (p8 b (b ◇ b) a b)
  have pw:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (pa a))).symm).trans ((h ((a ◇ a) ◇ a) b ((a ◇ a) ◇ a)).symm)
  have px:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (p0 a ((b ◇ b) ◇ b))).symm).trans (pw b (a ◇ (((b ◇ b) ◇ b) ◇ a)))
  have py:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) ((h a a a).symm)))).symm).trans (pu (a ◇ a))
  have pz:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ t) (pm a)).symm).trans (pl (a ◇ a) ((a ◇ a) ◇ a))
  have p10:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ (((a ◇ a) ◇ a) ◇ b)) ◇ a) ◇ t) (pd a a)).symm).trans (p8 ((a ◇ a) ◇ a) a b a)
  have p11:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (py a)))).trans (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p4 a)))).symm).trans (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)))) (pm a)))).symm).trans (p10 (a ◇ a) (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a))))
  have p12:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) ((h a a a).symm)).symm).trans (p11 (a ◇ a))
  have p13:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (pm a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p12 a)))).symm).trans (pv a (a ◇ a)))
  have p14:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (p11 a))).symm).trans ((h b (a ◇ a) (a ◇ (a ◇ a))).symm)
  have p15:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p12 b))).symm).trans ((h a ((b ◇ b) ◇ (b ◇ b)) b).symm)
  have p16:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ b))) (p11 a)).symm).trans ((h (a ◇ a) (a ◇ (a ◇ a)) b).symm)
  have p17:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ t) (p3 a))).symm).trans (p16 a ((a ◇ a) ◇ (a ◇ a)))
  have p18:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p11 a))).symm).trans ((h (a ◇ (a ◇ a)) b (a ◇ a)).symm)
  have p19:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p3 a))).symm).trans (p18 a ((a ◇ a) ◇ (a ◇ a)))
  have p1a:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b))) (p12 a)).symm).trans ((h ((a ◇ a) ◇ (a ◇ a)) a b).symm)
  have p1b:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b)) ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a))).symm).trans (p8 (a ◇ a) (a ◇ a) b (a ◇ a))
  have p1c:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (pv (a ◇ a) a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p11 a))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => (((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ a)) ◇ t) (p17 a)))).symm).trans (p1b a ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ a)))
  have p1d:=fun (a:G)=>by
    exact (((p4 a).symm).trans (((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1c a)).symm).trans (ps a))).symm
  have p1e:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1d a))).symm).trans (pi a a)
  have p1f:=fun (a:G)=>by
    exact ((((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) (p1e a))).trans (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p1e a)))).symm).trans (((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)))) (p1e a)).symm).trans (p3 (((a ◇ a) ◇ a) ◇ a)))).symm
  have p1g:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (p1f a)).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1f a))).symm).trans (p1e a)
  have p1h:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1d a)).symm).trans (((cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p1f a)).symm).trans (pl a a))).symm
  have p1i:=fun (a:G)=>by
    exact (((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a))).trans (pa a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1h (a ◇ a)))).symm).trans (pz a))).symm
  have p1j:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p1c a))).symm).trans (pd a (a ◇ a))
  have p1k:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1j a)).symm).trans (p19 a)
  have p1l:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) ((h a a a).symm)).symm).trans (p1k (a ◇ a))).trans (p3 a)
  have p1m:=fun (a:G)=>by
    exact (((p1k a).symm).trans (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1l (a ◇ a)))).symm).trans (pp a))).symm
  have p1n:=fun (a:G)=>by
    exact ((((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a)))) (p1m a))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1m a)))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1g a))).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))))) (p1m a)).symm).trans (p3 ((a ◇ a) ◇ (a ◇ a))))
  have p1o:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a)))) (p1g a)).symm).trans (p1c (a ◇ (a ◇ a)))).trans (p1g a))
  have p1p:=fun (a:G)=>by
    exact (((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (p1g a))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => a ◇ t) (p1g a)))).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))).symm).trans (p13 (a ◇ (a ◇ a)))).trans (p1g a))
  have p1q:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (p1h a)).symm).trans (p1c a)
  have p1r:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p1g a))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (p1k a)).symm).trans (p14 a (a ◇ (a ◇ a))))
  have p1s:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))).symm).trans (p1d (a ◇ (a ◇ a)))
  have p1t:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (pa a))).symm).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1h (a ◇ a)))).symm).trans (p1a a (a ◇ a)))
  have p1u:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1m a)).symm).trans (p1h ((a ◇ a) ◇ (a ◇ a)))).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1m a))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1j a))).trans (p1i a))
  have p1v:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1i a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (p1m a)).symm).trans (p13 (a ◇ a)))
  have p1w:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p1m a))).symm).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a)))) (p1l a))).symm).trans (p1a a ((a ◇ a) ◇ (a ◇ a))))
  have p1x:=fun (a b c d e:G)=>by
    exact ((cg (fun t => (((c ◇ (a ◇ e)) ◇ (((b ◇ a) ◇ (e ◇ b)) ◇ c)) ◇ d) ◇ t) (cg (fun t => t ◇ (d ◇ e)) (p5 e a b c))).symm).trans ((h d ((c ◇ (a ◇ e)) ◇ (((b ◇ a) ◇ (e ◇ b)) ◇ c)) e).symm)
  have p1y:=fun (a b c d e:G)=>by
    exact ((cg (fun t => (e ◇ d) ◇ t) (cg (fun t => (((c ◇ (a ◇ d)) ◇ (((b ◇ a) ◇ (d ◇ b)) ◇ c)) ◇ e) ◇ t) (p5 d a b c))).symm).trans ((h d e ((c ◇ (a ◇ d)) ◇ (((b ◇ a) ◇ (d ◇ b)) ◇ c))).symm)
  have p1z:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1h a)).symm).trans (pa a)
  have p20:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p1d b))).symm).trans ((h a ((b ◇ b) ◇ b) b).symm)
  have p21:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ (((a ◇ a) ◇ a) ◇ b))) (p1d a)).symm).trans ((h ((a ◇ a) ◇ a) a b).symm)
  have p22:=fun (a b:G)=>by
    exact ((((((((cg (fun t => t ◇ (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (a ◇ a))) (cg (fun t => a ◇ t) (p1f a)))))).trans (cg (fun t => t ◇ (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p1f a))))))).trans (cg (fun t => ((((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => a ◇ t) (p1f a)))))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (p11 a)))))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1p a))))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (p1d a)))).trans (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p1z a)))).symm).trans (((cg (fun t => t ◇ (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (a ◇ a))) ◇ t) (px a a)))).symm).trans (p1x (((a ◇ a) ◇ a) ◇ a) a (a ◇ (((a ◇ a) ◇ a) ◇ a)) b (a ◇ a)))
  have p23:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ (b ◇ b)))) (p1l b))).symm).trans ((h a b ((b ◇ b) ◇ (b ◇ b))).symm)
  have p24:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) ◇ t) (p1q a)).symm).trans (p8 (a ◇ a) a b a)
  have p25:=fun (a b:G)=>by
    exact ((((((((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (a ◇ a))) (cg (fun t => a ◇ t) (p1f a))))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p1f a)))))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (p11 a))))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => ((((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => a ◇ t) (p1f a)))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1p a)))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (p1d a))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1z a)))).symm).trans (((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (a ◇ a))) ◇ t) (px a a))))).symm).trans (p1y (((a ◇ a) ◇ a) ◇ a) a (a ◇ (((a ◇ a) ◇ a) ◇ a)) (a ◇ a) b))
  have p26:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p1h b))).symm).trans ((h a b (b ◇ b)).symm)
  have p27:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b))) (p1f a)).symm).trans ((h a ((a ◇ a) ◇ a) b).symm)
  have p28:=fun (a b:G)=>by
    exact ((((cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a)))).trans (cg (fun t => t ◇ (a ◇ (a ◇ (a ◇ (a ◇ a))))) (cg (fun t => ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ t) (p1g a)))).trans (cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ a) ◇ t) (p1o a))).symm).trans ((((cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a)))) (p27 a b))).symm).trans (p25 (a ◇ (a ◇ a)) ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)))).trans (p1g a))
  have p29:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (p1g a))).symm).trans ((h b (a ◇ (a ◇ a)) (a ◇ (a ◇ a))).symm)
  have p2a:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (p3 a)))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))) (cg (fun t => t ◇ b) ((h a a a).symm))).symm).trans (p29 (a ◇ a) b))
  have p2b:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ (((b ◇ (a ◇ a)) ◇ (a ◇ b)) ◇ a)) (p1d a))).symm).trans (p5 a (a ◇ a) b a)
  have p2c:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) ((h b b a).symm))).symm).trans (pg b ((a ◇ b) ◇ (b ◇ a)))
  have p2d:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1n a)))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p1g a))))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ a)) (p1u a)))).symm).trans (((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1g a))))).symm).trans (p26 b (a ◇ (a ◇ a))))
  have p2e:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p1f b))).symm).trans ((h ((b ◇ b) ◇ b) a b).symm)
  have p2f:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => t ◇ b) ((h b b a).symm))).symm).trans (pl b ((a ◇ b) ◇ (b ◇ a)))
  have p2g:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ b))) (p1g a)).symm).trans ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) b).symm)
  have p2h:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p3 a)))).symm).trans ((((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ b)) (cg (fun t => b ◇ t) ((h a a a).symm)))).symm).trans (p2g (a ◇ a) b)).trans (p3 a))
  have p2i:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (p1g a))).symm).trans ((h (a ◇ (a ◇ a)) b (a ◇ (a ◇ a))).symm)
  have p2j:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ b) (p3 a)))).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ b) ◇ (a ◇ a))) (cg (fun t => b ◇ t) ((h a a a).symm))).symm).trans (p2i (a ◇ a) b)).trans (p3 a))
  have p2k:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ a))) ◇ (a ◇ b))) (p1n a)).symm).trans ((h a (a ◇ (a ◇ a)) b).symm)
  have p2l:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ ((a ◇ a) ◇ b))) (p1m a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (cg (fun t => b ◇ t) ((h a a a).symm)))).symm).trans (p2k (a ◇ a) b))
  have p2m:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (p1c b))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (p2f a b))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p2f a b)))).symm).trans (p0 (b ◇ b) (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)))).trans ((cg (fun t => (b ◇ b) ◇ t) (p2f a b)).trans (p1c b)))
  have p2n:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (p2c a b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ b))) (p2m a b)).symm).trans (p20 (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) b))).symm
  have p2o:=fun (a b:G)=>by
    exact ((((cg (fun t => ((b ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (p12 b)).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p2h b a))).trans (p12 b)).symm).trans (((cg (fun t => ((b ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p2n a b))).symm).trans (pd b ((a ◇ b) ◇ (b ◇ a))))
  have p2p:=fun (a b c:G)=>by
    exact (((p2o a c).symm).trans (p2o b c)).symm
  have p2q:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (p2o a b)).symm).trans (p1l b)
  have p2r:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (p2o a b)).symm).trans (p1h (b ◇ b))).trans (cg (fun t => (b ◇ b) ◇ t) (p3 b))
  have p2s:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1m b)).symm).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b)))) (p2o a b)).symm).trans (p3 (b ◇ b)))
  have p2t:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1m b)).symm).trans ((((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))) ◇ t) (p2o a b)).symm).trans (p1i (b ◇ b))).trans (p1i b))
  have p2u:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p2o a c)))).symm).trans (p23 b c)
  have p2v:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pa a)).trans (pa a)).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (pa a)).symm).trans (p2o b ((a ◇ a) ◇ a)))).symm
  have p2w:=fun (a b c d:G)=>by
    exact ((cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ (b ◇ a)) ◇ t) ((h a b c).symm)).symm).trans (p2p d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a))
  have p2x:=fun (a b c d:G)=>by
    exact ((p2w a b c d).symm).trans (p2w a b c a)
  have p2y:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ (b ◇ a))))) (p0 a b)).symm).trans ((p2o (b ◇ (a ◇ (b ◇ a))) b).symm)
  have p2z:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (pw a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p2v a b)))).symm).trans (p0 (((a ◇ a) ◇ a) ◇ b) (b ◇ ((a ◇ a) ◇ a)))).trans (((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p2x a (a ◇ a) ((b ◇ ((a ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ b)) b)).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p1f a)))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1d a)))))).symm
  have p30:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => t ◇ b) (p2r c a))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ a)) (p2o c a)))).symm).trans (p2z (a ◇ a) b)).trans ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => b ◇ t) (p1i a))).trans (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p1i a))))
  have p31:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (pv a b)).symm).trans ((p2o (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) (b ◇ b)).symm)).trans (p1m b)
  have p32:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a))) (p24 a b)).symm).trans ((p2o (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) (a ◇ a)).symm)).trans (p1m a)
  have p33:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ a) ◇ (a ◇ b))) ((p2o a b).symm)).symm).trans (p2p c (a ◇ b) (b ◇ a))).trans (p2x a b ((c ◇ (b ◇ a)) ◇ ((b ◇ a) ◇ c)) c)
  have p34:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ ((c ◇ b) ◇ (b ◇ c))) (p2p a b c)).symm).trans (p2p d (b ◇ c) (c ◇ b))).trans (p2x b c ((d ◇ (c ◇ b)) ◇ ((c ◇ b) ◇ d)) d)
  have p35:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ t) (p1l a)).symm).trans (((cg (fun t => ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p24 a b))).symm).trans (p2a (a ◇ a) (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)))
  have p36:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (p10 b a)).symm).trans ((p2o (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b) b).symm)
  have p37:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (p28 b a)).symm).trans ((p2o (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b) b).symm)
  have p38:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) ((p2o b a).symm)).symm).trans (p33 a b a)
  have p39:=fun (a b c:G)=>by
    exact ((cg (fun t => ((c ◇ c) ◇ (c ◇ c)) ◇ t) (p2p a c b)).symm).trans (p33 b c a)
  have p3a:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((b ◇ d) ◇ (d ◇ b)) ◇ t) (p2p a d c)).symm).trans (p34 b c d a)
  have p3b:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ a) ◇ c) ◇ t) (cg (fun t => t ◇ (c ◇ (a ◇ b))) ((p2o a b).symm))).symm).trans ((h c (b ◇ a) (a ◇ b)).symm)
  have p3c:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ a) (pd b (a ◇ b)))).symm).trans (pb a b b (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))))
  have p3d:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) ◇ ((b ◇ b) ◇ c))) (pv a b)).symm).trans ((h (b ◇ b) (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) c).symm)
  have p3e:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (p31 a b)).trans (p11 b)).symm).trans (((cg (fun t => (b ◇ ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) ◇ t) (p3d a b (b ◇ b))).symm).trans (p2u b ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) b))).symm
  have p3f:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ t) (p1i b))))).trans (cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (pv a b)))))).trans (cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (p1d b))))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) (pv a b)))).trans (cg (fun t => t ◇ (b ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (p4 b))).trans (p2b b a)).symm).trans ((((cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => ((b ◇ b) ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b)))) ◇ t) (p3e a b))).symm).trans (p3c (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) (b ◇ b))).trans (p3e a b))
  have p3g:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (a ◇ b)) ◇ ((b ◇ a) ◇ c))) ((p2o a b).symm)).symm).trans ((h (b ◇ a) (a ◇ b) c).symm)
  have p3h:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ (b ◇ a)) ◇ (b ◇ (a ◇ b))) ◇ t) (p3g a b b)).symm).trans (p3b (b ◇ a) b (b ◇ (a ◇ b)))
  have p3i:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (p1d b))).trans (cg (fun t => (b ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) ◇ t) (p21 b a))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p36 a b))).trans (p1t b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (cg (fun t => b ◇ t) (p21 b a)))).symm).trans (p3h ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) b))).symm
  have p3j:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p10 b a))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (p1l b))).trans (p3i a b)).symm).trans (((cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (cg (fun t => t ◇ ((((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b) ◇ b)) (p3i a b))).symm).trans (p2q b (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)))).symm
  have p3k:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ t) (p3 b)).trans (cg (fun t => t ◇ b) (p21 b a))).trans (p1f b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p3j a b))).symm).trans (p2a b ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))).symm
  have p3l:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p1r a))).symm).trans ((h (a ◇ (a ◇ a)) b ((a ◇ a) ◇ a)).symm)
  have p3m:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ ((a ◇ a) ◇ c))) (p24 a b)).symm).trans ((h (a ◇ a) (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) c).symm)
  have p3n:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (p32 b a)).trans (p11 b)).symm).trans (((cg (fun t => (b ◇ ((b ◇ b) ◇ (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b))) ◇ t) (p3m b a (b ◇ b))).symm).trans (p2u b ((b ◇ b) ◇ (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b)) b))).symm
  have p3o:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ a) (p3n b a)).symm).trans (p35 a b)).symm
  have p3p:=fun (a b:G)=>by
    exact (((((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (pa b)).trans (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p2l b a))).trans (p1c b)).symm).trans (((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p3o b a))).symm).trans (p2d b ((a ◇ b) ◇ ((b ◇ b) ◇ a))))).symm
  have p3q:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ b) (p1g a))).symm).trans (p3p b (a ◇ (a ◇ a)))).trans (p1g a)
  have p3r:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ (a ◇ (a ◇ a))))) (p3q a b)).symm).trans ((p2o (b ◇ (a ◇ (a ◇ a))) (a ◇ b)).symm)).trans (p2x b a (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ b) ◇ (a ◇ b))) (a ◇ b))).symm
  have p3s:=fun (a b c:G)=>by
    exact (((p3r a c).symm).trans (p2p b c (a ◇ c))).symm
  have p3t:=fun (a b c:G)=>by
    exact (p3s a b c).trans ((p3s a a c).symm)
  have p3u:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (((a ◇ ((c ◇ c) ◇ c)) ◇ (c ◇ a)) ◇ c))) (p28 c a))).symm).trans ((h b c (((a ◇ ((c ◇ c) ◇ c)) ◇ (c ◇ a)) ◇ c)).symm)
  have p3v:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1f b)))).trans (cg (fun t => t ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) (p1o b))).symm).trans ((((cg (fun t => (b ◇ (b ◇ (((b ◇ b) ◇ b) ◇ b))) ◇ t) (p5 b ((b ◇ b) ◇ b) a b)).symm).trans (p3u a (b ◇ (((b ◇ b) ◇ b) ◇ b)) b)).trans (cg (fun t => b ◇ t) (p1f b)))
  have p3w:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (p1o b))).trans (cg (fun t => (b ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) ◇ t) (p3v a b))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ b)))) (p37 a b))).trans (p1w b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => b ◇ t) (p3v a b)))).symm).trans (p3h ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) b))).symm
  have p3x:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p28 b a))).trans (cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (p1l b))).trans (p3w a b)).symm).trans (((cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (cg (fun t => t ◇ ((((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ b)) (p3w a b))).symm).trans (p2q b (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)))).symm
  have p3y:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) ◇ t) (p3 b)).trans (cg (fun t => t ◇ b) (p3v a b))).trans (p0 b b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p3x a b))).symm).trans (p2a b ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))))).symm
  have p3z:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))))) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (p1i b))))).trans (cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p1m b)))).trans (cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ a))) ◇ t) (p1v b))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (pg b a))).trans (p3 b)).symm).trans ((((cg (fun t => (b ◇ ((a ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p3x a (b ◇ b)))).symm).trans (p22 b ((a ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (p1i b))))).symm
  have p40:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (pl b a)).symm).trans ((((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p3z a b)))).symm).trans (p0 ((b ◇ b) ◇ a) (a ◇ ((b ◇ b) ◇ b)))).trans (cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p3z a b)))
  have p41:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (p2e a b)).trans (p40 a b)).symm).trans ((((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p3y a b)))).symm).trans (p0 (b ◇ a) (a ◇ ((b ◇ b) ◇ b)))).trans (cg (fun t => (b ◇ a) ◇ t) (p3y a b)))
  have p42:=fun (a b c:G)=>by
    exact (p30 b c a).trans (p40 c b)
  have p43:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ c) (p2o a b))).symm).trans (p41 c (b ◇ b))).trans (cg (fun t => ((b ◇ b) ◇ c) ◇ t) (p3 b))
  have p44:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p40 b a)).symm).trans (pi a b)
  have p45:=fun (a b:G)=>by
    exact ((((p42 ((((b ◇ b) ◇ b) ◇ ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ ((b ◇ b) ◇ b)) b ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))).trans (cg (fun t => t ◇ b) (p16 b a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ b) ◇ ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => t ◇ b) (p16 b a))).symm).trans (p44 b ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))))).symm
  have p46:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (p2h a c))).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p2o c a)))).symm).trans (p45 b (a ◇ a))).trans (p1i a))
  have p47:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p3 b))).symm).trans ((((cg (fun t => (c ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b)))) ◇ t) (cg (fun t => t ◇ c) (p2o a b))).symm).trans (p45 c (b ◇ b))).trans (p1i b))
  have p48:=fun (a b c:G)=>by
    exact (((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (p1r b)))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p3a a a b b))))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1r b))))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (p1g b)))).symm).trans ((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (p3a a a b b)))).symm).trans (p46 ((a ◇ b) ◇ (b ◇ a)) c a)).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p3a a a b b)).trans (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1r b))).trans (p2t a b)))
  have p49:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p48 b a b)).symm).trans (((cg (fun t => ((b ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ (a ◇ b)) ◇ t) (p48 a b ((b ◇ a) ◇ (a ◇ b)))).symm).trans (p47 (b ◇ a) (a ◇ b) (b ◇ ((b ◇ a) ◇ (a ◇ b)))))).symm
  have p4a:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p1r b))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p3a a a b b))).symm).trans (p3f c ((a ◇ b) ◇ (b ◇ a)))).trans ((p3a a a b b).trans (p1r b)))
  have p4b:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p3a a c a a)).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p1r a))).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p2o c a))).symm).trans (p38 b (a ◇ a)))).symm
  have p4c:=fun (a b c d:G)=>by
    exact ((((cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p3a a d a a)).trans (cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p1r a))).symm).trans ((((cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p2o d a))).symm).trans (p39 b c (a ◇ a))).trans (p4b a c ((c ◇ ((a ◇ a) ◇ c)) ◇ (((a ◇ a) ◇ c) ◇ c))))).symm
  have p4d:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ c) ◇ (c ◇ c))) (p2h a d)).symm).trans ((((cg (fun t => t ◇ ((c ◇ c) ◇ (c ◇ c))) (cg (fun t => (a ◇ a) ◇ t) (p2o d a))).symm).trans (p4c (a ◇ a) b c d)).trans (cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p3 a)))
  have p4e:=fun (a b c d:G)=>by
    exact ((p4d b c d a).symm).trans (p4d b b d a)
  have p4f:=fun (a b:G)=>by
    exact (((cg (fun t => a ◇ t) (p1s b)).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1h b))).symm).trans (p4e a a b (b ◇ b)))).symm
  have p4g:=fun (a b c d:G)=>by
    exact ((p4c b c d a).symm).trans (p4c b b d a)
  have p4h:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p2p a b (c ◇ c))).symm).trans (p4f b c)
  have p4i:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (cg (fun t => (((b ◇ b) ◇ a) ◇ c) ◇ t) (p3p a b))).symm).trans ((h (a ◇ b) c ((b ◇ b) ◇ a)).symm)
  have p4j:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ a))) (p1d b))).symm).trans (pk a ((b ◇ b) ◇ b) b)
  have p4k:=fun (a b c:G)=>by
    exact (((p4g ((a ◇ (a ◇ a)) ◇ ((c ◇ c) ◇ (c ◇ c))) a c c).symm).trans (((p4b a c a).symm).trans (p2p b c ((a ◇ a) ◇ c)))).symm
  have p4l:=fun (a b c:G)=>by
    exact (((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1r b)))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (p2t a b)))).symm).trans ((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p3a a a b b)))).symm).trans (p3k c ((a ◇ b) ◇ (b ◇ a)))).trans (((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p3a a a b b)).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1r b))).trans (p2s a b)))
  have p4m:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (p1u a))).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1m a)))).symm).trans (p3y b ((a ◇ a) ◇ (a ◇ a)))).trans ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1m a)).trans (p1j a)))
  have p4n:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p49 ((a ◇ a) ◇ (a ◇ a)) b))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1m a)))))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p1u a))))).trans (cg (fun t => ((((a ◇ a) ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ t) (p43 a a b))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ a)) (p3y ((a ◇ a) ◇ a) b))).symm).trans (((cg (fun t => ((((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ t) (p4m a b))).symm).trans (p20 (b ◇ ((a ◇ a) ◇ a)) (((a ◇ a) ◇ (a ◇ a)) ◇ b)))
  have p4o:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1r b)))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p2t a b)))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p3a a a b b)))).symm).trans (p3y c ((a ◇ b) ◇ (b ◇ a)))).trans (((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p3a a a b b)).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1r b))).trans (p2s a b)))
  have p4p:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ t) (p49 a b))).trans (cg (fun t => t ◇ (b ◇ b)) (p4l b a ((b ◇ b) ◇ b)))).symm).trans (((cg (fun t => ((((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b))) ◇ t) (p4l a b ((b ◇ a) ◇ (a ◇ b)))).symm).trans (p4o (b ◇ a) (a ◇ b) (((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b)))))).symm
  have p4q:=fun (a b:G)=>by
    exact ((((((cg (fun t => ((a ◇ b) ◇ ((a ◇ a) ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p4p a b))).trans (p3t (a ◇ a) (a ◇ b) (b ◇ b))).trans (p4k a (a ◇ a) (b ◇ b))).trans (p4h a (a ◇ (a ◇ a)) b)).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b))) (cg (fun t => (a ◇ b) ◇ t) (p4p a b))).symm).trans (p1r (a ◇ b))).trans (cg (fun t => (a ◇ b) ◇ t) (p4p a b)))).symm
  have p4r:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (pc a b))).trans (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (p4j a b))).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4j a b)))).symm).trans (p0 (b ◇ (a ◇ (b ◇ a))) (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))).trans ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4j a b)).trans (pc a b)))
  have p4s:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4j a b)).trans (pc a b)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ (a ◇ (b ◇ a))))) (p4r a b)).symm).trans ((p2o (b ◇ (a ◇ (b ◇ a))) (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))).symm)).trans (((((((((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (p4p ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b)))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b)))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p4p ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a)))))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b)))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b)))).trans (p4p ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b))).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b))))).symm
  have p4t:=fun (a b:G)=>by
    exact ((((((p4p (b ◇ (a ◇ (b ◇ a))) (b ◇ (b ◇ b))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p1g b))).trans (cg (fun t => t ◇ b) (pc a b))).trans (p0 a b)).symm).trans (((cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p4s a b))).symm).trans (p3l b (b ◇ (a ◇ (b ◇ a)))))).symm
  have p4u:=fun (a b c:G)=>by
    exact (((p4t a c).symm).trans (p4t b c)).symm
  have p4v:=fun (a b:G)=>by
    exact (((p3 a).symm).trans (((cg (fun t => (a ◇ a) ◇ t) ((p2o a a).symm)).symm).trans (p4t b (a ◇ a)))).symm
  have p4w:=fun (a b:G)=>by
    exact (((((((cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4s a b))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p4s a b)))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p4s a b))).trans (cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (pc a b))).trans (pc a b)).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4s a b))).symm).trans (p2y (b ◇ (a ◇ (b ◇ a))) ((b ◇ b) ◇ b))).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ b) ◇ b))) (pa b)).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pa b))).trans (pa b)))
  have p4x:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (p4t a b)).symm).trans (p1n b)
  have p4y:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) ((p4t b a).symm)).symm).trans ((p4t (a ◇ b) b).symm)
  have p4z:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p3 a)))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p4y a b))).trans (p1g b)).symm).trans ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p4y a (a ◇ a))))).symm).trans (p4n (a ◇ (a ◇ a)) b)).trans ((cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))).trans (cg (fun t => b ◇ t) (p4w a a))))).symm
  have p50:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ c) ◇ t) (p4u a c b)).symm).trans ((p4t (b ◇ c) c).symm)
  have p51:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ (c ◇ b))) (p4v a c)).symm).trans (p50 b c ((a ◇ a) ◇ c))).trans (((cg (fun t => ((a ◇ a) ◇ c) ◇ t) (p4p (a ◇ a) c)).trans (p4q (a ◇ a) c)).trans (cg (fun t => t ◇ (c ◇ (c ◇ c))) (p3 a)))).symm
  have p52:=fun (a b c:G)=>by
    exact ((p51 a b c).symm).trans (p51 a a c)
  have p53:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((c ◇ b) ◇ (a ◇ c)) ◇ t) ((h a b c).symm)).symm).trans (p4u d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a))
  have p54:=fun (a b c d:G)=>by
    exact ((p53 a b c d).symm).trans (p53 a b c a)
  have p55:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ a) ◇ t) (p3f a b)).symm).trans (p4u c (b ◇ a) (a ◇ (b ◇ b)))).symm
  have p56:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (p3 c)).symm).trans (((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (p50 a b (c ◇ c))).symm).trans (p55 b c (a ◇ (b ◇ a))))
  have p57:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ b) ◇ b) ◇ t) (p4v a b)).symm).trans ((p2o ((a ◇ a) ◇ b) b).symm)
  have p58:=fun (a b c:G)=>by
    exact (((p12 b).symm).trans ((((cg (fun t => b ◇ t) (p4x c b)).symm).trans (p4u a b (c ◇ (b ◇ c)))).trans (cg (fun t => a ◇ t) (p56 c b a)))).symm
  have p59:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p4z a b))).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p4 a))).symm).trans (p53 b (a ◇ a) ((a ◇ a) ◇ a) c)).trans (p54 b (a ◇ a) (c ◇ (((a ◇ a) ◇ b) ◇ c)) c))).symm
  have p5a:=fun (a b:G)=>by
    exact (((p59 a b a).symm).trans ((p4t b ((a ◇ a) ◇ b)).symm)).trans ((((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p4p (a ◇ a) b)).trans (p4q (a ◇ a) b)).trans (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p3 a))).trans (p52 a b b))
  have p5b:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (c ◇ b)) ◇ t) (p4u a (c ◇ (b ◇ (c ◇ b))) c)).symm).trans (pj b c)
  have p5c:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ b)) ◇ t) ((p4t (b ◇ b) a).symm)).symm).trans (p4v b (a ◇ (b ◇ b)))
  have p5d:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ (b ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (p3 b))).trans (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p54 a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p1d a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b))) ◇ ((a ◇ a) ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p5c (b ◇ b) a))).symm).trans (p4i (a ◇ a) b ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b)))))
  have p5e:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p3 a)).symm).trans (((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) ((p2o a a).symm))).symm).trans (p5c (a ◇ a) b))
  have p5f:=fun (a b c:G)=>by
    exact ((((((cg (fun t => t ◇ (((c ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ c)) ◇ b)) (cg (fun t => b ◇ t) (p1l a))).trans (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p3t a c a)))).trans (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p1r a)))).trans (cg (fun t => (b ◇ a) ◇ t) (p56 a a b))).trans (p5d (b ◇ a) b)).symm).trans ((((cg (fun t => t ◇ (((c ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ c)) ◇ b)) (cg (fun t => b ◇ t) (p5d (a ◇ a) a))).symm).trans (p4a c (a ◇ a) b)).trans (p3 a))
  have p5g:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p4z (b ◇ a) b))).symm).trans (((cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ (((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ a))))) (p5f a b a)).symm).trans (pd (b ◇ a) b))
  have p5h:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ b))) (cg (fun t => a ◇ t) (p4z a b))).trans (cg (fun t => (a ◇ b) ◇ t) (p54 a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => (a ◇ b) ◇ t) (p1d a))).symm).trans (((cg (fun t => (a ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (pd a b))).symm).trans (p5g (a ◇ (b ◇ ((a ◇ a) ◇ a))) ((a ◇ a) ◇ b)))
  have p5i:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => a ◇ t) (p2j a b))).symm).trans (((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ ((b ◇ a) ◇ ((a ◇ b) ◇ (a ◇ a)))) (p2j a b))).symm).trans (p5f ((a ◇ b) ◇ (a ◇ a)) (b ◇ a) a))).symm
  have p5j:=fun (a b c:G)=>by
    exact ((p5h (b ◇ b) a).symm).trans ((((cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p3p a b)).symm).trans (p4u c ((b ◇ b) ◇ a) (a ◇ b))).trans (p54 b a (c ◇ ((a ◇ b) ◇ c)) c))
  have p5k:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ b) (p3a a c a a)).trans (cg (fun t => t ◇ b) (p1r a))).trans (p56 a a b)).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p2o c a))).symm).trans (p5j b (a ◇ a) c)).trans ((p55 b a (a ◇ a)).trans (p5i a b)))
  have p5l:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ a)) (p59 b a (a ◇ (((b ◇ b) ◇ a) ◇ a)))).symm).trans (((cg (fun t => t ◇ (a ◇ a)) (p5j (b ◇ b) a a)).symm).trans (p5e (a ◇ a) b))
  have p5m:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ a)) (p5l a b)).symm).trans (p5a ((b ◇ a) ◇ a) (a ◇ a))).trans ((cg (fun t => ((b ◇ a) ◇ a) ◇ t) (p54 a a (((b ◇ a) ◇ a) ◇ ((a ◇ a) ◇ ((b ◇ a) ◇ a))) ((b ◇ a) ◇ a))).trans (cg (fun t => ((b ◇ a) ◇ a) ◇ t) (p1d a)))).symm
  have p5n:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ b) (p5e b a))).symm).trans (p5l b ((b ◇ b) ◇ (a ◇ a)))).symm
  have p5o:=fun (a b c:G)=>by
    exact (p56 a b c).trans (p5k b c ((c ◇ b) ◇ (c ◇ c)))
  have p5p:=fun (a b c:G)=>by
    exact ((((((cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p5o c a b)).trans (p4p (a ◇ a) (b ◇ a))).trans (p5j ((b ◇ a) ◇ (b ◇ a)) a (((a ◇ a) ◇ (a ◇ a)) ◇ ((b ◇ a) ◇ (b ◇ a))))).trans (p59 (b ◇ a) a (a ◇ ((((b ◇ a) ◇ (b ◇ a)) ◇ a) ◇ a)))).trans (p5m a b)).symm).trans ((((cg (fun t => t ◇ ((c ◇ (a ◇ c)) ◇ b)) (p5o c a b)).symm).trans (p4p (c ◇ (a ◇ c)) b)).trans (cg (fun t => t ◇ (b ◇ b)) (p5b c c a)))
  have p5q:=fun (a b:G)=>by
    exact (((((cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (cg (fun t => t ◇ a) (p1m a)))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (p1n a)))).trans (cg (fun t => a ◇ t) (p1l a))).symm).trans ((((p5j (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) a a).symm).trans (p4t b ((a ◇ a) ◇ (a ◇ a)))).trans (cg (fun t => b ◇ t) (p5j b a (((a ◇ a) ◇ (a ◇ a)) ◇ b))))).symm
  have p5r:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ b) (p5f a b a))).symm).trans (p5l b ((b ◇ a) ◇ (b ◇ a)))).symm
  have p5s:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (p5g b a)).symm).trans (p5k ((a ◇ b) ◇ a) b a)).trans ((((((((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ a))) (cg (fun t => t ◇ ((a ◇ b) ◇ a)) (p5h a b))).trans (cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ a))) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p5h a b)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) ◇ t) (cg (fun t => b ◇ t) (p5h a b)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) ◇ t) (p54 a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) ◇ t) (p1d a))).trans (cg (fun t => t ◇ a) (p4p (a ◇ a) b))).trans (cg (fun t => t ◇ a) (p5j (b ◇ b) a (((a ◇ a) ◇ (a ◇ a)) ◇ (b ◇ b))))).trans (cg (fun t => t ◇ a) (p59 b a (a ◇ (((b ◇ b) ◇ a) ◇ a)))))).symm
  have p5t:=fun (a b c d:G)=>by
    exact (((p54 a b (c ◇ ((b ◇ a) ◇ c)) c).symm).trans ((((cg (fun t => c ◇ t) (cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (p5b d d a)))).symm).trans (p55 b (d ◇ (a ◇ d)) c)).trans ((cg (fun t => t ◇ ((d ◇ (a ◇ d)) ◇ (d ◇ (a ◇ d)))) (p5o d a b)).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p5b d d a))))).symm
  have p5u:=fun (a b c:G)=>by
    exact (((p59 a c a).symm).trans (p4u b c ((a ◇ a) ◇ c))).symm
  have p5v:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (p4u a b (c ◇ b))).symm).trans (p5q b c)
  have p5w:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p5g c a)))).symm).trans (p5v b ((a ◇ c) ◇ a) c)).trans (((((cg (fun t => t ◇ ((a ◇ c) ◇ a)) (p5h a c)).trans (cg (fun t => ((a ◇ a) ◇ c) ◇ t) (p5h a c))).trans (p4p (a ◇ a) c)).trans (p5j (c ◇ c) a (((a ◇ a) ◇ (a ◇ a)) ◇ (c ◇ c)))).trans (p5u c a a))
  have p5x:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ b) ◇ (b ◇ b)) ◇ t) (p4v a b)).symm).trans (p3f ((a ◇ a) ◇ b) b)
  have p5y:=fun (a b:G)=>by
    exact ((((((((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ a) ◇ (a ◇ a))) ◇ t) (p5j (a ◇ a) b (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ a)))).trans (cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ a) ◇ (a ◇ a))) ◇ t) (p5u a b b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (p5j (((b ◇ b) ◇ a) ◇ (a ◇ a)) b (((b ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ a) ◇ (a ◇ a)))))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p5x b a))))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (p54 a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (p1d a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p5x b a))).symm).trans (p15 (((b ◇ b) ◇ a) ◇ (a ◇ a)) b))).symm
  have p5z:=fun (a b c d:G)=>by
    exact ((p53 a b c d).trans ((p53 a b a d).symm)).trans ((cg (fun t => t ◇ a) (p5i a b)).trans (p5t a b (((a ◇ a) ◇ (b ◇ a)) ◇ a) (((a ◇ a) ◇ (b ◇ a)) ◇ a)))
  have p60:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ (b ◇ b)) ◇ (b ◇ b)))) (p5j (a ◇ b) b (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ b)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ (b ◇ b)) ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (p5s b a)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ (b ◇ b)) ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (p5p a b (b ◇ (a ◇ a)))))).trans (p5w (a ◇ (b ◇ b)) (b ◇ b) (b ◇ (a ◇ (b ◇ b))))).trans (p5s (a ◇ (b ◇ b)) b)).symm).trans (((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ b)) ◇ t) (p5z (b ◇ b) a (b ◇ b) a)).symm).trans (p4i a b ((b ◇ b) ◇ (b ◇ b))))
  have p61:=fun (a b c d:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (c ◇ b)) ◇ t) (p4v a (c ◇ b))).symm).trans ((p53 b c d ((a ◇ a) ◇ (c ◇ b))).symm)).trans (p5z b c d (((d ◇ c) ◇ (b ◇ d)) ◇ b))
  have p62:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p5i b c)).symm).trans (((p58 b c a).trans ((p58 c c a).symm)).trans (p12 c))
  have p63:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (p5n (a ◇ a) b)).trans (cg (fun t => b ◇ t) (p5y b a))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p57 b a))).symm).trans (p62 a b (((b ◇ b) ◇ a) ◇ a))).trans ((((((((((((((((((cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ (((b ◇ b) ◇ a) ◇ a))) (p4p ((b ◇ b) ◇ a) a)).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ (((b ◇ b) ◇ a) ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (p4p (b ◇ b) a)))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ (((b ◇ b) ◇ a) ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (p5j (a ◇ a) b (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ a)))))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ (((b ◇ b) ◇ a) ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (p5u a b b)))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (p4p ((b ◇ b) ◇ a) a))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p4p (b ◇ b) a)))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p5j (a ◇ a) b (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ a)))))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p5u a b b)))).trans (p4p ((a ◇ b) ◇ b) (a ◇ a))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p4p (a ◇ b) b))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (p4p a b)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p60 (a ◇ a) b))).trans (p5i (a ◇ a) b)).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p5p a b (b ◇ (a ◇ a))))).trans (p5j (a ◇ (b ◇ b)) a (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (b ◇ b))))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (p5h a (b ◇ b))))).trans (cg (fun t => a ◇ t) (p61 a b b (((a ◇ a) ◇ (b ◇ b)) ◇ a)))).trans (cg (fun t => a ◇ t) (p1d b))))
  have p64:=fun (a b:G)=>by
    exact ((((((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p5p a b (b ◇ (a ◇ a))))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ (b ◇ b)) ◇ t) (p5p a b (b ◇ (a ◇ a)))))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p5r (b ◇ b) a))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p5y a b))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p63 b a)))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p5p a (b ◇ (a ◇ a)) a))).symm).trans (p63 (a ◇ a) b))
  exact (calc
    ((x ◇ y) ◇ x)=((x ◇ x) ◇ y):=p5h x y
    _=(y ◇ (y ◇ (y ◇ x))):=(p64 x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19023_to_58445 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19023_to_58445
