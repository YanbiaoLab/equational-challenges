-- Equation6678 → Equation6681
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
-- Conclusion: x = y ◇ (x ◇ ((x ◇ z) ◇ (z ◇ y)))
-- Original submission SHA-256: 848f9586041e4f054812f3f10cd2fadd8abd625e6635f00787c72e645c5b0a68
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ z) ◇ (z ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ (b ◇ a)) ◇ a) ◇ t) ((h (b ◇ (b ◇ a)) b a).symm)).symm).trans ((h b ((b ◇ (b ◇ a)) ◇ a) (b ◇ a)).symm)
  have p1:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a a a)
  have p2:=fun (a b c:G)=>by
    exact ((h a a a).trans (p1 a a a)).symm
  have p3:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (p2 a (a ◇ (a ◇ ((a ◇ a) ◇ (a ◇ a)))) (a ◇ (a ◇ ((a ◇ a) ◇ (a ◇ a)))))).symm).trans (((cg (fun t => t ◇ (a ◇ (a ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p2 a a a))).symm).trans (p0 ((a ◇ a) ◇ (a ◇ a)) a))
  have p4:=fun (a:G)=>by
    exact (((((cg (fun t => t ◇ ((a ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ a))) (cg (fun t => t ◇ a) (p3 a))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (p3 a)))).trans (cg (fun t => (a ◇ a) ◇ t) (p3 a))).symm).trans (((cg (fun t => t ◇ ((a ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ a))) (cg (fun t => t ◇ a) (cg (fun t => (a ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (p3 a)))).symm).trans (p0 a (a ◇ ((a ◇ a) ◇ (a ◇ a)))))).symm
  have p5:=fun (a b c d:G)=>by
    exact ((cg (fun t => a ◇ t) (p4 a)).symm).trans (p2 a a a)
  have p6:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ a) (p4 a)).symm).trans (p3 a)
  have p7:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p5 a (a ◇ ((a ◇ a) ◇ a)) (a ◇ ((a ◇ a) ◇ a)) (a ◇ ((a ◇ a) ◇ a))))).symm).trans (((cg (fun t => t ◇ (a ◇ (a ◇ ((a ◇ a) ◇ a)))) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => a ◇ t) (p5 a a a a)))).symm).trans (p0 ((a ◇ a) ◇ a) a))
  have p8:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p6 b)))).symm).trans ((h a ((b ◇ b) ◇ b) b).symm)
  have p9:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p6 a))).symm).trans (p8 (a ◇ a) a)
  have pa:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p9 a))).symm).trans ((h (a ◇ a) (a ◇ a) a).symm)
  have pb:=fun (a:G)=>by
    exact (((cg (fun t => ((((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (pa a))).trans (p6 ((a ◇ a) ◇ (a ◇ a)))).symm).trans (((cg (fun t => ((((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (pa a)))).symm).trans (p8 (a ◇ a) ((a ◇ a) ◇ (a ◇ a))))
  have pc:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (pb a))).symm).trans ((h a a a).symm)
  have pd:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p5 a a a a)))).symm).trans ((h a b ((a ◇ a) ◇ a)).symm)
  have pe:=fun (a b c d:G)=>by
    exact ((cg (fun t => d ◇ t) (cg (fun t => c ◇ t) (cg (fun t => t ◇ (d ◇ (a ◇ ((a ◇ b) ◇ (c ◇ b))))) ((h a c b).symm)))).symm).trans ((h c d (a ◇ ((a ◇ b) ◇ (c ◇ b)))).symm)
  have pf:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) ((h a b a).symm)))).symm).trans (pe a a b b)
  have pg:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (pf a b)).symm).trans (((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => b ◇ t) (pf a (b ◇ (a ◇ a))))).symm).trans ((h b (b ◇ (a ◇ a)) (a ◇ a)).symm))
  have ph:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ ((b ◇ (a ◇ a)) ◇ b))) (cg (fun t => t ◇ b) (pg a b))).trans (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (pg a b)))).trans (cg (fun t => (b ◇ b) ◇ t) (pg a b))).symm).trans (((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ ((b ◇ (a ◇ a)) ◇ b))) (cg (fun t => t ◇ b) (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (pg a b)))).symm).trans (p0 b (b ◇ (a ◇ a))))).symm
  have pi:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ (a ◇ a)) ◇ t) (pg a (b ◇ b))).symm).trans (pf b ((b ◇ b) ◇ (a ◇ a)))
  have pj:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ (b ◇ b)) (pb b))).trans (cg (fun t => t ◇ (b ◇ b)) (pb b))).trans (pb b)).symm).trans (((cg (fun t => t ◇ (b ◇ b)) (ph a (b ◇ b))).symm).trans (pi a b))).symm
  have pk:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ (a ◇ a)))) (cg (fun t => t ◇ (a ◇ a)) (pj a a))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (pj a b)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (pj a a))).trans (cg (fun t => (a ◇ a) ◇ t) (pj b b))).trans (pj b a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (pj a b)))).symm).trans (p8 (b ◇ b) (a ◇ a)))).symm
  have pl:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (pk a b))).symm).trans (p5 b a a a)
  have pm:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (pk a b))).symm).trans (p6 b)
  have pn:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (((a ◇ a) ◇ b) ◇ b))) (cg (fun t => t ◇ b) (pm a b))).trans (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (pm a b)))).trans (cg (fun t => (b ◇ b) ◇ t) (pm a b))).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (((a ◇ a) ◇ b) ◇ b))) (cg (fun t => t ◇ b) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (pm a b)))).symm).trans (p0 b ((a ◇ a) ◇ b)))
  have po:=fun (a b c:G)=>by
    exact ((((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (c ◇ c)) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (ph c a)))))).trans (cg (fun t => b ◇ t) (cg (fun t => (a ◇ (c ◇ c)) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (pl a a)))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ a))) (ph c a)))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (c ◇ c)) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (pf c (a ◇ (c ◇ c)))))))).symm).trans (pe a (c ◇ c) (a ◇ (c ◇ c)) b)).trans (ph c a))
  have pp:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (cg (fun t => t ◇ (b ◇ c)) (pk a c)))).symm).trans ((h c b c).symm)
  have pq:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (cg (fun t => (b ◇ c) ◇ t) (pk a c)))).symm).trans ((h b c c).symm)
  have pr:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (cg (fun t => t ◇ b) (pk a b))).symm).trans (p9 b)
  have ps:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ c) ◇ t) (cg (fun t => t ◇ c) (pk a c))).symm).trans (pr b c)
  have pt:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p9 a)).symm).trans (pn b ((a ◇ a) ◇ a))).symm
  have pu:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ b)) (ps a a b)).symm).trans (pn c ((a ◇ a) ◇ b))).symm
  have pv:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (cg (fun t => b ◇ t) (pl b b))).symm).trans (((cg (fun t => (((b ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (pg a ((b ◇ b) ◇ b))))).symm).trans (pd b (((b ◇ b) ◇ b) ◇ (a ◇ a))))
  have pw:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (p7 a)).symm).trans (pf a ((a ◇ a) ◇ ((a ◇ a) ◇ a)))
  have px:=fun (a b c d:G)=>by
    exact ((cg (fun t => d ◇ t) (cg (fun t => c ◇ t) (cg (fun t => (c ◇ (a ◇ ((a ◇ b) ◇ (d ◇ b)))) ◇ t) ((h a d b).symm)))).symm).trans ((h c d (a ◇ ((a ◇ b) ◇ (d ◇ b)))).symm)
  have py:=fun (a b c:G)=>by
    exact (((pu a b c).symm).trans (((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => t ◇ b) (pk a b))).symm).trans (pt b c))).symm
  have pz:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ ((b ◇ c) ◇ c))) (cg (fun t => t ◇ c) (pk a c))).symm).trans (p8 b c)
  have p10:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ c) (pk a c)))).symm).trans (pv b c)
  have p11:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (pk a b))).symm).trans (pw b)
  have p12:=fun (a b:G)=>by
    exact (((((((cg (fun t => ((((a ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ b))) ◇ b) ◇ t) (cg (fun t => ((a ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ t) (p11 a b))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ b)))) (cg (fun t => t ◇ b) (ps b a ((b ◇ b) ◇ b))))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ b)))) (cg (fun t => t ◇ b) (ps b b b)))).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (ps b a ((b ◇ b) ◇ b)))).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (ps b b b))).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ (((a ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ b))) (cg (fun t => t ◇ b) (cg (fun t => ((a ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ t) (p11 a b)))).symm).trans (p0 b ((a ◇ a) ◇ ((b ◇ b) ◇ b))))).symm
  have p13:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (ph b (a ◇ b)))).symm).trans ((h a b b).symm)
  have p14:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (b ◇ c)) (pk a (b ◇ c))))).symm).trans (p13 b c)
  have p15:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ c)) (pk a c)).symm).trans ((py b c a).symm)).trans (p12 c c)
  have p16:=fun (a b c d:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ d) ◇ (c ◇ c)) ◇ t) (pk a d)).symm).trans (p10 b c d)
  have p17:=fun (a b c:G)=>by
    exact ((cg (fun t => ((c ◇ a) ◇ ((b ◇ b) ◇ a)) ◇ t) (cg (fun t => c ◇ t) ((h c (b ◇ b) a).symm))).symm).trans (p14 b c ((c ◇ a) ◇ ((b ◇ b) ◇ a)))
  have p18:=fun (a b c d:G)=>by
    exact (((((((cg (fun t => t ◇ (((c ◇ a) ◇ ((b ◇ b) ◇ a)) ◇ ((c ◇ a) ◇ ((b ◇ b) ◇ a)))) (cg (fun t => c ◇ t) (pj c d))).trans (cg (fun t => t ◇ (((c ◇ a) ◇ ((b ◇ b) ◇ a)) ◇ ((c ◇ a) ◇ ((b ◇ b) ◇ a)))) (ph d c))).trans (ph ((c ◇ a) ◇ ((b ◇ b) ◇ a)) ((c ◇ c) ◇ c))).trans (cg (fun t => t ◇ ((c ◇ c) ◇ c)) (ps c c c))).trans (p15 c c c)).symm).trans (((cg (fun t => t ◇ (((c ◇ a) ◇ ((b ◇ b) ◇ a)) ◇ ((c ◇ a) ◇ ((b ◇ b) ◇ a)))) (cg (fun t => t ◇ ((d ◇ d) ◇ (c ◇ c))) (p17 a b c))).symm).trans (p17 (c ◇ c) d ((c ◇ a) ◇ ((b ◇ b) ◇ a))))).symm
  have p19:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ a) ◇ t) (cg (fun t => (c ◇ a) ◇ t) (p17 a b c))).symm).trans (pq c (c ◇ a) ((b ◇ b) ◇ a))
  have p1a:=fun (a b c:G)=>by
    exact (((cg (fun t => ((c ◇ c) ◇ b) ◇ t) (p0 b a)).symm).trans (p19 b c (a ◇ (a ◇ b)))).symm
  have p1b:=fun (a b c:G)=>by
    exact ((p1a a b c).symm).trans (p1a a b a)
  have p1c:=fun (a b:G)=>by
    exact ((p1b a b b).symm).trans (((cg (fun t => t ◇ a) ((pn a b).symm)).symm).trans ((p1a a b a).symm))
  have p1d:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ b) (po a (c ◇ c) a)).symm).trans (p1b b (((a ◇ a) ◇ a) ◇ (a ◇ ((c ◇ c) ◇ a))) c)).trans ((cg (fun t => t ◇ b) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pl c a)))).trans (cg (fun t => t ◇ b) (cg (fun t => (b ◇ b) ◇ t) (pm a a))))).symm
  have p1e:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ b) (po a (b ◇ b) a)).symm).trans (p1c b (((a ◇ a) ◇ a) ◇ (a ◇ ((b ◇ b) ◇ a))))).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ ((b ◇ b) ◇ a)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pl b a))))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ ((b ◇ b) ◇ a)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (pm a a))))).trans (cg (fun t => (b ◇ (b ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pl b a)))).trans (cg (fun t => (b ◇ (b ◇ a)) ◇ t) (pm a a)))).symm
  have p1f:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (pk a c))).symm).trans (p1d b c a)).symm
  have p1g:=fun (a b:G)=>by
    exact (((ph (b ◇ a) b).symm).trans ((((cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ a))) ((h b b a).symm)).symm).trans (p1e ((b ◇ a) ◇ (b ◇ a)) b)).trans ((cg (fun t => t ◇ b) (cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ a))) (pj (b ◇ a) (b ◇ a)))).trans (cg (fun t => t ◇ b) (pj (b ◇ a) (b ◇ a)))))).symm
  have p1h:=fun (a b c:G)=>by
    exact (((ps c b b).symm).trans ((((cg (fun t => t ◇ ((c ◇ c) ◇ b)) (p1g a b)).symm).trans (p18 b c ((b ◇ a) ◇ (b ◇ a)) a)).trans ((((cg (fun t => t ◇ (((b ◇ a) ◇ (b ◇ a)) ◇ ((b ◇ a) ◇ (b ◇ a)))) (cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ a))) (pj (b ◇ a) (b ◇ a)))).trans (cg (fun t => t ◇ (((b ◇ a) ◇ (b ◇ a)) ◇ ((b ◇ a) ◇ (b ◇ a)))) (pj (b ◇ a) (b ◇ a)))).trans (cg (fun t => ((b ◇ a) ◇ (b ◇ a)) ◇ t) (pj (b ◇ a) (b ◇ a)))).trans (pj (b ◇ a) (b ◇ a))))).symm
  have p1i:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ a)) (p1h a b a)).symm).trans (pn c (b ◇ a))).symm
  have p1j:=fun (a b c d:G)=>by
    exact (((cg (fun t => (c ◇ c) ◇ t) (p19 a d b)).symm).trans (p1i ((b ◇ a) ◇ b) ((d ◇ d) ◇ a) c)).trans ((cg (fun t => t ◇ (((d ◇ d) ◇ a) ◇ ((b ◇ a) ◇ b))) (ps d d a)).trans (cg (fun t => (a ◇ a) ◇ t) (p19 a d b)))
  have p1k:=fun (a b c:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ c) ◇ (b ◇ b)) ◇ t) (p16 ((((a ◇ a) ◇ c) ◇ (b ◇ b)) ◇ a) a b c)).symm).trans ((h (((a ◇ a) ◇ c) ◇ (b ◇ b)) (((a ◇ a) ◇ c) ◇ (b ◇ b)) a).symm)
  have p1l:=fun (a b c d:G)=>by
    exact (((p1k b a d).symm).trans (((cg (fun t => t ◇ d) (cg (fun t => ((b ◇ b) ◇ d) ◇ t) (pk a c))).symm).trans (p1k b c d))).symm
  have p1m:=fun (a b c d:G)=>by
    exact (((p1l a b c d).symm).trans (p1l b b c d)).symm
  have p1n:=fun (a b c d:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (p1j b (b ◇ a) c ((c ◇ c) ◇ ((b ◇ a) ◇ b)))).symm).trans ((((cg (fun t => t ◇ ((c ◇ c) ◇ ((b ◇ a) ◇ b))) (p19 a d b)).symm).trans (p18 ((b ◇ a) ◇ b) c ((d ◇ d) ◇ a) a)).trans ((((cg (fun t => t ◇ (((d ◇ d) ◇ a) ◇ ((d ◇ d) ◇ a))) (cg (fun t => t ◇ ((d ◇ d) ◇ a)) (ps d d a))).trans (cg (fun t => t ◇ (((d ◇ d) ◇ a) ◇ ((d ◇ d) ◇ a))) (p15 a d a))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (ps d d a))).trans (p16 a a a a)))
  have p1o:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (c ◇ c) ◇ t) (cg (fun t => t ◇ c) (pp a c b)))).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ ((c ◇ (b ◇ ((a ◇ a) ◇ (c ◇ b)))) ◇ c))) (pp a c b)).symm).trans (p1n (b ◇ ((a ◇ a) ◇ (c ◇ b))) c a a))
  have p1p:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (c ◇ c) ◇ t) (cg (fun t => t ◇ c) (p14 a b c)))).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ ((c ◇ (b ◇ ((a ◇ a) ◇ (b ◇ c)))) ◇ c))) (p14 a b c)).symm).trans (p1n (b ◇ ((a ◇ a) ◇ (b ◇ c))) c a a))
  have p1q:=fun (a b c d:G)=>by
    exact (((cg (fun t => c ◇ t) (cg (fun t => t ◇ a) (p1h ((d ◇ d) ◇ (c ◇ a)) a ((a ◇ ((d ◇ d) ◇ (c ◇ a))) ◇ (a ◇ ((d ◇ d) ◇ (c ◇ a))))))).symm).trans ((((cg (fun t => c ◇ t) (cg (fun t => ((a ◇ ((d ◇ d) ◇ (c ◇ a))) ◇ (a ◇ ((d ◇ d) ◇ (c ◇ a)))) ◇ t) (pp d c a))).symm).trans (p1p b c (a ◇ ((d ◇ d) ◇ (c ◇ a))))).trans (cg (fun t => c ◇ t) (cg (fun t => (b ◇ b) ◇ t) (pp d c a))))).symm
  have p1r:=fun (a b c:G)=>by
    exact (((p1o a b c).symm).trans (p1o b b c)).symm
  have p1s:=fun (a b c d:G)=>by
    exact (((cg (fun t => c ◇ t) (cg (fun t => t ◇ (c ◇ d)) (pk a d))).symm).trans (p1o b c d)).symm
  have p1t:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b))) (ps a a b))).trans (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (ps a a b)))).trans (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p1h b b ((b ◇ b) ◇ (b ◇ b))))).symm).trans ((p1o ((a ◇ a) ◇ b) ((a ◇ a) ◇ b) ((a ◇ a) ◇ b)).trans ((p1m (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) a a b).symm))
  have p1u:=fun (a b:G)=>by
    exact ((p1o a b a).trans (p1q (a ◇ b) a b a)).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p1h b a ((a ◇ b) ◇ (a ◇ b)))))
  have p1v:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ ((a ◇ a) ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ b) (p1u a b)))).trans (p1n ((a ◇ a) ◇ (a ◇ b)) b ((b ◇ ((a ◇ a) ◇ (a ◇ b))) ◇ ((b ◇ b) ◇ ((b ◇ ((a ◇ a) ◇ (a ◇ b))) ◇ b))) ((b ◇ ((a ◇ a) ◇ (a ◇ b))) ◇ ((b ◇ b) ◇ ((b ◇ ((a ◇ a) ◇ (a ◇ b))) ◇ b))))).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ ((b ◇ ((a ◇ a) ◇ (b ◇ a))) ◇ b))) (p1u a b)).symm).trans (p1n ((a ◇ a) ◇ (b ◇ a)) b a a))).symm
  have p1w:=fun (a b c d:G)=>by
    exact ((p16 c b d (b ◇ a)).symm).trans (((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ (d ◇ d)) (p1v b a))).symm).trans (p16 c b d (a ◇ b)))
  have p1x:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ a)) (p1w a b (b ◇ a) (b ◇ a))).trans (cg (fun t => (a ◇ b) ◇ t) (p1w a b (b ◇ a) (b ◇ a)))).symm).trans (p1h a b c)
  have p1y:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ a) (cg (fun t => b ◇ t) (p1w a b (b ◇ a) (b ◇ a)))).trans (cg (fun t => t ◇ a) (p1w (a ◇ b) b (b ◇ (a ◇ b)) (b ◇ (a ◇ b))))).symm).trans (p1e a b)
  have p1z:=fun (a b:G)=>by
    exact (((p1b a b b).symm).trans ((((p1y b a a a).symm).trans (p1w b ((b ◇ a) ◇ a) a a)).trans ((cg (fun t => b ◇ t) (cg (fun t => t ◇ a) (p1w a b (b ◇ a) (b ◇ a)))).trans (p1w ((a ◇ b) ◇ a) b (b ◇ ((a ◇ b) ◇ a)) (b ◇ ((a ◇ b) ◇ a)))))).symm
  have p20:=fun (a b c:G)=>by
    exact (((p1w ((a ◇ a) ◇ (b ◇ c)) c (c ◇ ((a ◇ a) ◇ (b ◇ c))) (c ◇ ((a ◇ a) ◇ (b ◇ c)))).symm).trans ((((p1r a c b).symm).trans (p1q (b ◇ c) c c a)).trans (((cg (fun t => c ◇ t) (cg (fun t => t ◇ (b ◇ c)) (p1x b c ((b ◇ c) ◇ (b ◇ c)) ((b ◇ c) ◇ (b ◇ c))))).trans (cg (fun t => c ◇ t) (p1w (b ◇ c) (c ◇ c) ((c ◇ c) ◇ (b ◇ c)) ((c ◇ c) ◇ (b ◇ c))))).trans (p1w ((b ◇ c) ◇ (c ◇ c)) c (c ◇ ((b ◇ c) ◇ (c ◇ c))) (c ◇ ((b ◇ c) ◇ (c ◇ c))))))).symm
  have p21:=fun (a b c:G)=>by
    exact (((((((cg (fun t => b ◇ t) (cg (fun t => t ◇ (c ◇ b)) (cg (fun t => t ◇ (c ◇ b)) (p1w b c (c ◇ b) (c ◇ b))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (c ◇ b)) (cg (fun t => (b ◇ c) ◇ t) (p1w b c (c ◇ b) (c ◇ b)))))).trans (cg (fun t => b ◇ t) (cg (fun t => ((b ◇ c) ◇ (b ◇ c)) ◇ t) (p1w b c (c ◇ b) (c ◇ b))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (b ◇ c)) (p1x b c ((b ◇ c) ◇ (b ◇ c)) ((b ◇ c) ◇ (b ◇ c)))))).trans (cg (fun t => b ◇ t) (p1w (b ◇ c) (c ◇ c) ((c ◇ c) ◇ (b ◇ c)) ((c ◇ c) ◇ (b ◇ c))))).trans (p1w ((b ◇ c) ◇ (c ◇ c)) b (b ◇ ((b ◇ c) ◇ (c ◇ c))) (b ◇ ((b ◇ c) ◇ (c ◇ c))))).symm).trans ((((cg (fun t => b ◇ t) ((pn a (c ◇ b)).symm)).symm).trans (p1s a a b c)).trans (p1w ((a ◇ a) ◇ (b ◇ c)) b (b ◇ ((a ◇ a) ◇ (b ◇ c))) (b ◇ ((a ◇ a) ◇ (b ◇ c)))))
  have p22:=fun (a b c d:G)=>by
    exact (((((cg (fun t => a ◇ t) (cg (fun t => (c ◇ c) ◇ t) (p1w ((a ◇ b) ◇ b) a (a ◇ ((a ◇ b) ◇ b)) (a ◇ ((a ◇ b) ◇ b))))).trans (cg (fun t => a ◇ t) (cg (fun t => (c ◇ c) ◇ t) (p1y a b (((a ◇ b) ◇ b) ◇ a) (((a ◇ b) ◇ b) ◇ a))))).trans (cg (fun t => a ◇ t) (p1w (((a ◇ a) ◇ a) ◇ b) (c ◇ c) ((c ◇ c) ◇ (((a ◇ a) ◇ a) ◇ b)) ((c ◇ c) ◇ (((a ◇ a) ◇ a) ◇ b))))).trans (p1w ((((a ◇ a) ◇ a) ◇ b) ◇ (c ◇ c)) a (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ (c ◇ c))) (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ (c ◇ c))))).symm).trans ((((cg (fun t => t ◇ ((c ◇ c) ◇ (a ◇ ((a ◇ b) ◇ b)))) (pz d a b)).symm).trans (p18 (a ◇ ((a ◇ b) ◇ b)) c ((d ◇ d) ◇ b) d)).trans (((((cg (fun t => t ◇ (((d ◇ d) ◇ b) ◇ ((d ◇ d) ◇ b))) (cg (fun t => t ◇ ((d ◇ d) ◇ b)) (p1x (d ◇ d) b (((d ◇ d) ◇ b) ◇ ((d ◇ d) ◇ b)) (((d ◇ d) ◇ b) ◇ ((d ◇ d) ◇ b))))).trans (cg (fun t => t ◇ (((d ◇ d) ◇ b) ◇ ((d ◇ d) ◇ b))) (p1w ((d ◇ d) ◇ b) (b ◇ b) ((b ◇ b) ◇ ((d ◇ d) ◇ b)) ((b ◇ b) ◇ ((d ◇ d) ◇ b))))).trans (cg (fun t => t ◇ (((d ◇ d) ◇ b) ◇ ((d ◇ d) ◇ b))) (p1t d b))).trans (cg (fun t => (((d ◇ d) ◇ b) ◇ (d ◇ d)) ◇ t) (p1x (d ◇ d) b (((d ◇ d) ◇ b) ◇ ((d ◇ d) ◇ b)) (((d ◇ d) ◇ b) ◇ ((d ◇ d) ◇ b))))).trans (p16 b d d b)))
  have p23:=fun (a b:G)=>by
    exact ((((((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (p1w (a ◇ a) a (a ◇ (a ◇ a)) (a ◇ (a ◇ a))))))).trans (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p1w ((a ◇ a) ◇ a) b (b ◇ ((a ◇ a) ◇ a)) (b ◇ ((a ◇ a) ◇ a))))))).trans (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p1w (((a ◇ a) ◇ a) ◇ b) a (a ◇ (((a ◇ a) ◇ a) ◇ b)) (a ◇ (((a ◇ a) ◇ a) ◇ b)))))).trans (cg (fun t => b ◇ t) (p1w ((((a ◇ a) ◇ a) ◇ b) ◇ a) a (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ a)) (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ a))))).trans (p1w (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a) b (b ◇ (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a)) (b ◇ (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a)))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (pc a)))).symm).trans ((h a b (a ◇ (a ◇ a))).symm))
  have p24:=fun (a b:G)=>by
    exact ((((((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p1w (b ◇ b) b (b ◇ (b ◇ b)) (b ◇ (b ◇ b))))))).trans (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ b) (p1w ((b ◇ b) ◇ b) a (a ◇ ((b ◇ b) ◇ b)) (a ◇ ((b ◇ b) ◇ b))))))).trans (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ b) (p1b a b b))))).trans (cg (fun t => b ◇ t) (p1w ((((a ◇ a) ◇ b) ◇ a) ◇ b) a (a ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ b)) (a ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ b))))).trans (p1w (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a) b (b ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a)) (b ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a)))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ (b ◇ (b ◇ b))) ◇ t) (pc b)))).symm).trans ((h a b (b ◇ (b ◇ b))).symm))
  have p25:=fun (a b:G)=>by
    exact ((((((cg (fun t => b ◇ t) (cg (fun t => ((((a ◇ a) ◇ a) ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (pm a a))))).trans (cg (fun t => b ◇ t) (cg (fun t => ((((a ◇ a) ◇ a) ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1w a b (b ◇ a) (b ◇ a)))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ b))) (cg (fun t => t ◇ a) (pm a a))))).trans (cg (fun t => b ◇ t) (p1w (((a ◇ a) ◇ a) ◇ (a ◇ b)) (a ◇ a) ((a ◇ a) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ b))) ((a ◇ a) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ b)))))).trans (p1w ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a)) b (b ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a))) (b ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a))))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => ((((a ◇ a) ◇ a) ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (p8 (((a ◇ a) ◇ a) ◇ a) a))))).symm).trans (pe ((a ◇ a) ◇ a) a ((((a ◇ a) ◇ a) ◇ a) ◇ a) b)).trans (cg (fun t => t ◇ a) (pm a a)))
  have p26:=fun (a b c:G)=>by
    exact (((((cg (fun t => t ◇ (c ◇ ((a ◇ a) ◇ a))) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1w b c (c ◇ b) (c ◇ b))))).trans (cg (fun t => (a ◇ ((a ◇ b) ◇ (b ◇ c))) ◇ t) (p1w ((a ◇ a) ◇ a) c (c ◇ ((a ◇ a) ◇ a)) (c ◇ ((a ◇ a) ◇ a))))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ c)) (p1w ((a ◇ b) ◇ (b ◇ c)) a (a ◇ ((a ◇ b) ◇ (b ◇ c))) (a ◇ ((a ◇ b) ◇ (b ◇ c)))))).trans (p1w (((a ◇ a) ◇ a) ◇ c) (((a ◇ b) ◇ (b ◇ c)) ◇ a) ((((a ◇ b) ◇ (b ◇ c)) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ c)) ((((a ◇ b) ◇ (b ◇ c)) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ c)))).symm).trans (((cg (fun t => (a ◇ ((a ◇ b) ◇ (c ◇ b))) ◇ t) (cg (fun t => c ◇ t) (ph (a ◇ ((a ◇ b) ◇ (c ◇ b))) a))).symm).trans (pe a b c (a ◇ ((a ◇ b) ◇ (c ◇ b)))))
  have p27:=fun (a b c:G)=>by
    exact (((p20 a b c).symm).trans (p20 b b c)).symm
  have p28:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ c) (cg (fun t => t ◇ (a ◇ a)) (p1w a c (c ◇ a) (c ◇ a)))).trans (cg (fun t => t ◇ c) (p1w (a ◇ a) (a ◇ c) ((a ◇ c) ◇ (a ◇ a)) ((a ◇ c) ◇ (a ◇ a))))).symm).trans (((p21 (c ◇ a) c a).trans (p1f b (c ◇ a) c)).trans ((cg (fun t => t ◇ c) (cg (fun t => (b ◇ b) ◇ t) (p1w a c (c ◇ a) (c ◇ a)))).trans (cg (fun t => t ◇ c) (p1w (a ◇ c) (b ◇ b) ((b ◇ b) ◇ (a ◇ c)) ((b ◇ b) ◇ (a ◇ c))))))).symm
  have p29:=fun (a b c:G)=>by
    exact (((cg (fun t => (((a ◇ a) ◇ b) ◇ c) ◇ t) (cg (fun t => c ◇ t) (p1w b c (c ◇ b) (c ◇ b)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ c) ◇ t) (p1w (b ◇ c) c (c ◇ (b ◇ c)) (c ◇ (b ◇ c))))).symm).trans (((cg (fun t => t ◇ (c ◇ (c ◇ b))) (p1a c b a)).symm).trans (p0 b c))
  have p2a:=fun (a b c:G)=>by
    exact (((((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ c) (p1w b c (c ◇ b) (c ◇ b))))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ ((b ◇ c) ◇ c))) (p1w b c (c ◇ b) (c ◇ b)))).trans (cg (fun t => (b ◇ c) ◇ t) (p1w ((b ◇ c) ◇ c) (a ◇ a) ((a ◇ a) ◇ ((b ◇ c) ◇ c)) ((a ◇ a) ◇ ((b ◇ c) ◇ c))))).trans (p1w (((b ◇ c) ◇ c) ◇ (a ◇ a)) (b ◇ c) ((b ◇ c) ◇ (((b ◇ c) ◇ c) ◇ (a ◇ a))) ((b ◇ c) ◇ (((b ◇ c) ◇ c) ◇ (a ◇ a))))).symm).trans (((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => t ◇ ((c ◇ b) ◇ c)) (pk a c))).symm).trans (p1n b c a a))
  have p2b:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ a) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ b)) (p1x a b ((a ◇ b) ◇ (a ◇ b)) ((a ◇ b) ◇ (a ◇ b)))))).trans (cg (fun t => t ◇ a) (cg (fun t => t ◇ b) (p1w (a ◇ b) (b ◇ b) ((b ◇ b) ◇ (a ◇ b)) ((b ◇ b) ◇ (a ◇ b)))))).trans (cg (fun t => t ◇ a) (p28 a b b))).symm).trans (((cg (fun t => ((((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)) ◇ b) ◇ t) (p2a b a b)).symm).trans (p26 (a ◇ b) b b))
  have p2c:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => t ◇ (d ◇ d)) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (pk a b))))).symm).trans (p22 b c d a)
  have p2d:=fun (a b:G)=>by
    exact (((((((((((((cg (fun t => a ◇ t) (cg (fun t => ((b ◇ a) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (b ◇ a)) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ b) (p1w a b (b ◇ a) (b ◇ a)))))))).trans (cg (fun t => a ◇ t) (cg (fun t => ((b ◇ a) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ b) ◇ b))) (p1w a b (b ◇ a) (b ◇ a))))))).trans (cg (fun t => a ◇ t) (cg (fun t => ((b ◇ a) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (b ◇ a)) (cg (fun t => (a ◇ b) ◇ t) (p1w ((a ◇ b) ◇ b) (b ◇ b) ((b ◇ b) ◇ ((a ◇ b) ◇ b)) ((b ◇ b) ◇ ((a ◇ b) ◇ b)))))))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (((a ◇ b) ◇ b) ◇ (b ◇ b))) ◇ (b ◇ a))) (cg (fun t => t ◇ (b ◇ a)) (p1w a b (b ◇ a) (b ◇ a)))))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (((a ◇ b) ◇ b) ◇ (b ◇ b))) ◇ (b ◇ a))) (cg (fun t => (a ◇ b) ◇ t) (p1w a b (b ◇ a) (b ◇ a)))))).trans (cg (fun t => a ◇ t) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (cg (fun t => ((a ◇ b) ◇ (((a ◇ b) ◇ b) ◇ (b ◇ b))) ◇ t) (p1w a b (b ◇ a) (b ◇ a)))))).trans (cg (fun t => a ◇ t) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p1w (((a ◇ b) ◇ b) ◇ (b ◇ b)) (a ◇ b) ((a ◇ b) ◇ (((a ◇ b) ◇ b) ◇ (b ◇ b))) ((a ◇ b) ◇ (((a ◇ b) ◇ b) ◇ (b ◇ b)))))))).trans (cg (fun t => a ◇ t) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p2a b a b))))).trans (cg (fun t => a ◇ t) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (p1w (a ◇ b) a (a ◇ (a ◇ b)) (a ◇ (a ◇ b)))))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ a)) (p1x a b ((a ◇ b) ◇ (a ◇ b)) ((a ◇ b) ◇ (a ◇ b)))))).trans (cg (fun t => a ◇ t) (p1w ((a ◇ b) ◇ a) (b ◇ b) ((b ◇ b) ◇ ((a ◇ b) ◇ a)) ((b ◇ b) ◇ ((a ◇ b) ◇ a))))).trans (p1w (((a ◇ b) ◇ a) ◇ (b ◇ b)) a (a ◇ (((a ◇ b) ◇ a) ◇ (b ◇ b))) (a ◇ (((a ◇ b) ◇ a) ◇ (b ◇ b))))).symm).trans ((((cg (fun t => t ◇ (((b ◇ a) ◇ (b ◇ a)) ◇ (((b ◇ a) ◇ ((b ◇ b) ◇ ((b ◇ a) ◇ b))) ◇ (b ◇ a)))) (p1n a b a a)).symm).trans (p1n ((b ◇ b) ◇ ((b ◇ a) ◇ b)) (b ◇ a) a a)).trans ((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ b) (p1w a b (b ◇ a) (b ◇ a)))).trans (p1w ((a ◇ b) ◇ b) (b ◇ b) ((b ◇ b) ◇ ((a ◇ b) ◇ b)) ((b ◇ b) ◇ ((a ◇ b) ◇ b)))))
  have p2e:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ (b ◇ b)) (p1w (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a) a (a ◇ (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a)) (a ◇ (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a))))).trans (p2a b ((((a ◇ a) ◇ a) ◇ b) ◇ a) a)).symm).trans ((((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a)) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a)) (p23 a b)))).symm).trans (p2d (((((a ◇ a) ◇ a) ◇ b) ◇ a) ◇ a) b)).trans (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ b) (p23 a b))))
  have p2f:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a)) (cg (fun t => t ◇ (b ◇ b)) (p1w (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a) a (a ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a)) (a ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a))))).trans (p2a b ((((a ◇ a) ◇ b) ◇ a) ◇ b) a)).symm).trans ((((cg (fun t => t ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a)) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a)) (p24 a b)))).symm).trans (p2d (((((a ◇ a) ◇ b) ◇ a) ◇ b) ◇ a) b)).trans (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ b) (p24 a b))))
  have p2g:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (p1w ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a)) (a ◇ a) ((a ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a))) ((a ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a)))))).trans (p2a b (((a ◇ a) ◇ a) ◇ (a ◇ b)) (a ◇ a))).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a))) (p25 a b)))).symm).trans (p2d ((((a ◇ a) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a)) b)).trans ((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ b) (p25 a b))).trans (p1t a b)))).symm
  have p2h:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (pk a b)))).symm).trans (p2e b c)
  have p2i:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ a)) (p1w a b (b ◇ a) (b ◇ a))).trans (p1w (a ◇ a) (a ◇ b) ((a ◇ b) ◇ (a ◇ a)) ((a ◇ b) ◇ (a ◇ a)))).symm).trans (((p2h a b a).symm).trans (p2f a b))).symm
  have p2j:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (cg (fun t => t ◇ c) (pk a b)))).symm).trans (p2f b c)).trans (p2i b c ((b ◇ c) ◇ (c ◇ c)))
  have p2k:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p1w a b (b ◇ a) (b ◇ a))).symm).trans ((((p2g b a).symm).trans (p1b (b ◇ b) a b)).trans (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ a) (p1x b b ((b ◇ b) ◇ (b ◇ b)) ((b ◇ b) ◇ (b ◇ b))))))
  have p2l:=fun (a b c:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ c)) (cg (fun t => t ◇ (((b ◇ c) ◇ c) ◇ ((b ◇ c) ◇ c))) (p1w (((a ◇ a) ◇ b) ◇ c) c (c ◇ (((a ◇ a) ◇ b) ◇ c)) (c ◇ (((a ◇ a) ◇ b) ◇ c))))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ c)) (cg (fun t => ((((a ◇ a) ◇ b) ◇ c) ◇ c) ◇ t) (p1x (b ◇ c) c (((b ◇ c) ◇ c) ◇ ((b ◇ c) ◇ c)) (((b ◇ c) ◇ c) ◇ ((b ◇ c) ◇ c)))))).trans (p2a c ((a ◇ a) ◇ b) c)).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ c)) (cg (fun t => t ◇ (((b ◇ c) ◇ c) ◇ ((b ◇ c) ◇ c))) (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ c)) (p29 a b c)))).symm).trans (p2d (((a ◇ a) ◇ b) ◇ c) ((b ◇ c) ◇ c))).trans (((cg (fun t => t ◇ (((b ◇ c) ◇ c) ◇ ((b ◇ c) ◇ c))) (cg (fun t => t ◇ ((b ◇ c) ◇ c)) (p29 a b c))).trans (cg (fun t => t ◇ (((b ◇ c) ◇ c) ◇ ((b ◇ c) ◇ c))) (p1w ((b ◇ c) ◇ c) c (c ◇ ((b ◇ c) ◇ c)) (c ◇ ((b ◇ c) ◇ c))))).trans (cg (fun t => (((b ◇ c) ◇ c) ◇ c) ◇ t) (p1x (b ◇ c) c (((b ◇ c) ◇ c) ◇ ((b ◇ c) ◇ c)) (((b ◇ c) ◇ c) ◇ ((b ◇ c) ◇ c))))))).symm
  have p2m:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ c) ◇ c)) (p2l a b c)).symm).trans (p2a c (b ◇ c) c)
  have p2n:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => t ◇ (c ◇ c)) (p1w a b (b ◇ a) (b ◇ a)))).trans (p28 a c b)).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ (c ◇ c)) (p2m a b a))).symm).trans (p2c a b ((b ◇ a) ◇ a) c)).trans (cg (fun t => t ◇ a) (p1w a b (b ◇ a) (b ◇ a))))
  have p2o:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ a) (p2n a b (((a ◇ a) ◇ (a ◇ b)) ◇ b))).symm).trans (p2b a b)
  have p2p:=fun (a b:G)=>by
    exact ((((p2o b a a).symm).trans (p1w b ((b ◇ a) ◇ b) a a)).trans ((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p1w a b (b ◇ a) (b ◇ a)))).trans (p1w ((a ◇ b) ◇ b) b (b ◇ ((a ◇ b) ◇ b)) (b ◇ ((a ◇ b) ◇ b))))).symm
  have p2q:=fun (a b c:G)=>by
    exact (((p2n b c (((b ◇ b) ◇ (b ◇ c)) ◇ c)).symm).trans (p27 a b c)).symm
  have p2r:=fun (a b c:G)=>by
    exact (p28 a b c).trans (p2n a c (((a ◇ a) ◇ (a ◇ c)) ◇ c))
  have p2s:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) ((h a c b).symm))).symm).trans (p2o c (a ◇ ((a ◇ b) ◇ (c ◇ b))) a)).trans ((cg (fun t => a ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1w b c (c ◇ b) (c ◇ b)))).trans (p1w ((a ◇ b) ◇ (b ◇ c)) a (a ◇ ((a ◇ b) ◇ (b ◇ c))) (a ◇ ((a ◇ b) ◇ (b ◇ c)))))).symm
  have p2t:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (p1w b c (c ◇ b) (c ◇ b))))).trans (cg (fun t => t ◇ c) (p1z b c))).trans (p2j b b c)).symm).trans ((((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p2s c a b))).symm).trans (p2p ((c ◇ a) ◇ (a ◇ b)) c)).trans ((cg (fun t => t ◇ (a ◇ b)) (p1w a c (c ◇ a) (c ◇ a))).trans (p1w (a ◇ b) (a ◇ c) ((a ◇ c) ◇ (a ◇ b)) ((a ◇ c) ◇ (a ◇ b)))))
  have p2u:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ a)) (p1w a b (b ◇ a) (b ◇ a)))))).trans (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1b a b b)))))).trans (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1w (((a ◇ a) ◇ b) ◇ a) (a ◇ b) ((a ◇ b) ◇ (((a ◇ a) ◇ b) ◇ a)) ((a ◇ b) ◇ (((a ◇ a) ◇ b) ◇ a))))))).trans (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (p1w ((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ b)) b (b ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ b))) (b ◇ ((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ b))))))).trans (cg (fun t => t ◇ b) (p1w (((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ b)) ◇ b) b (b ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ b)) ◇ b)) (b ◇ (((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ b)) ◇ b))))).trans (p2p ((((a ◇ a) ◇ b) ◇ a) ◇ (a ◇ b)) b)).symm).trans (((cg (fun t => (b ◇ (b ◇ ((b ◇ a) ◇ (((b ◇ b) ◇ b) ◇ a)))) ◇ t) (px b a b ((b ◇ b) ◇ b))).symm).trans (po b (b ◇ (b ◇ ((b ◇ a) ◇ (((b ◇ b) ◇ b) ◇ a)))) a))
  have p2v:=fun (a b c:G)=>by
    exact ((((((cg (fun t => t ◇ a) (cg (fun t => t ◇ b) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c))))))).trans (cg (fun t => t ◇ a) (cg (fun t => t ◇ b) (cg (fun t => (b ◇ b) ◇ t) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b)))))))).trans (cg (fun t => t ◇ a) (cg (fun t => t ◇ b) (cg (fun t => (b ◇ b) ◇ t) (p2s a c b))))).trans (cg (fun t => t ◇ a) (cg (fun t => t ◇ b) (p1w ((a ◇ b) ◇ b) (b ◇ b) ((b ◇ b) ◇ ((a ◇ b) ◇ b)) ((b ◇ b) ◇ ((a ◇ b) ◇ b)))))).trans (cg (fun t => t ◇ a) (p2r (a ◇ b) b b))).symm).trans ((((cg (fun t => (((b ◇ b) ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c)))) ◇ b) ◇ t) ((h a b c).symm)).symm).trans (p2u b (a ◇ ((a ◇ c) ◇ (b ◇ c))))).trans (((((((((((cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c)))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c)))) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c)))))).trans (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c)))) (cg (fun t => (a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c))))))).trans (cg (fun t => ((a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c)))))).trans (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b))))))).trans (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (p2s a c b)))).trans (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (cg (fun t => ((a ◇ b) ◇ b) ◇ t) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b))))))).trans (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (cg (fun t => ((a ◇ b) ◇ b) ◇ t) (p2s a c b)))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ ((a ◇ b) ◇ b)) ◇ t) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b)))))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ ((a ◇ b) ◇ b)) ◇ t) (p2s a c b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (p1x (a ◇ b) b (((a ◇ b) ◇ b) ◇ ((a ◇ b) ◇ b)) (((a ◇ b) ◇ b) ◇ ((a ◇ b) ◇ b))))).trans (p1w ((a ◇ b) ◇ b) (b ◇ b) ((b ◇ b) ◇ ((a ◇ b) ◇ b)) ((b ◇ b) ◇ ((a ◇ b) ◇ b)))))
  have p2w:=fun (a b c:G)=>by
    exact (((((((((((((((((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c))))) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c))))))).trans (cg (fun t => t ◇ b) (cg (fun t => (a ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c)))))))).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b))))) (cg (fun t => a ◇ t) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b)))))))).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b))))) (cg (fun t => a ◇ t) (p2s a c b))))).trans (cg (fun t => t ◇ b) (cg (fun t => (a ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => b ◇ t) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b)))))))).trans (cg (fun t => t ◇ b) (cg (fun t => (a ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => b ◇ t) (p2s a c b))))).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ b))) (p1w ((a ◇ b) ◇ b) a (a ◇ ((a ◇ b) ◇ b)) (a ◇ ((a ◇ b) ◇ b)))))).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ b))) (p1y a b (((a ◇ b) ◇ b) ◇ a) (((a ◇ b) ◇ b) ◇ a))))).trans (cg (fun t => t ◇ b) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p1w ((a ◇ b) ◇ b) b (b ◇ ((a ◇ b) ◇ b)) (b ◇ ((a ◇ b) ◇ b)))))).trans (cg (fun t => t ◇ b) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p2p a b)))).trans (cg (fun t => t ◇ b) (p2j a b a))).trans (cg (fun t => t ◇ b) (cg (fun t => (b ◇ b) ◇ t) (p1w a b (b ◇ a) (b ◇ a))))).trans (cg (fun t => t ◇ b) (p1w (a ◇ b) (b ◇ b) ((b ◇ b) ◇ (a ◇ b)) ((b ◇ b) ◇ (a ◇ b))))).trans (cg (fun t => t ◇ b) (p2i a b ((a ◇ b) ◇ (b ◇ b))))).trans (p2q a a b)).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c))))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c)))) ((h a b c).symm)))).symm).trans (p2v b (a ◇ ((a ◇ c) ◇ (b ◇ c))) a)).trans (((((((((((((((((cg (fun t => t ◇ ((a ◇ ((a ◇ c) ◇ (b ◇ c))) ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c))))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c)))) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c))))))).trans (cg (fun t => t ◇ ((a ◇ ((a ◇ c) ◇ (b ◇ c))) ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c))))) (cg (fun t => (b ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c))))))).trans (cg (fun t => ((b ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) ◇ t) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (b ◇ c)))) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c))))))).trans (cg (fun t => ((b ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) ◇ t) (cg (fun t => (a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p1w c b (b ◇ c) (b ◇ c))))))).trans (cg (fun t => t ◇ ((a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b))))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (cg (fun t => b ◇ t) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b)))))))).trans (cg (fun t => t ◇ ((a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b))))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (cg (fun t => b ◇ t) (p2s a c b))))).trans (cg (fun t => t ◇ ((a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b))))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (p1w ((a ◇ b) ◇ b) b (b ◇ ((a ◇ b) ◇ b)) (b ◇ ((a ◇ b) ◇ b)))))).trans (cg (fun t => t ◇ ((a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b))))) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (p2p a b)))).trans (cg (fun t => t ◇ ((a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b))))) (cg (fun t => a ◇ t) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b))))))).trans (cg (fun t => t ◇ ((a ◇ ((a ◇ c) ◇ (c ◇ b))) ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b))))) (cg (fun t => a ◇ t) (p2s a c b)))).trans (cg (fun t => (a ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b))))))).trans (cg (fun t => (a ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ ((a ◇ c) ◇ (c ◇ b)))) (p2s a c b)))).trans (cg (fun t => (a ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => ((a ◇ b) ◇ b) ◇ t) (p1w ((a ◇ c) ◇ (c ◇ b)) a (a ◇ ((a ◇ c) ◇ (c ◇ b))) (a ◇ ((a ◇ c) ◇ (c ◇ b))))))).trans (cg (fun t => (a ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => ((a ◇ b) ◇ b) ◇ t) (p2s a c b)))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ b) ◇ ((a ◇ b) ◇ b))) (p1w ((a ◇ b) ◇ b) a (a ◇ ((a ◇ b) ◇ b)) (a ◇ ((a ◇ b) ◇ b))))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ b) ◇ ((a ◇ b) ◇ b))) (p1y a b (((a ◇ b) ◇ b) ◇ a) (((a ◇ b) ◇ b) ◇ a)))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p1x (a ◇ b) b (((a ◇ b) ◇ b) ◇ ((a ◇ b) ◇ b)) (((a ◇ b) ◇ b) ◇ ((a ◇ b) ◇ b))))))).symm
  have p2x:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (p2k (a ◇ b) a)).trans (p1w (((a ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a)) b (b ◇ (((a ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a))) (b ◇ (((a ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a))))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p2w a b a))).symm).trans ((h ((a ◇ a) ◇ a) b b).symm))
  have p2y:=fun (a b c:G)=>by
    exact ((((((cg (fun t => t ◇ (a ◇ c)) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ c))) (p1x a b ((a ◇ b) ◇ (a ◇ b)) ((a ◇ b) ◇ (a ◇ b)))))).trans (cg (fun t => t ◇ (a ◇ c)) (cg (fun t => ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ c))) ◇ t) (p1x a b ((a ◇ b) ◇ (a ◇ b)) ((a ◇ b) ◇ (a ◇ b)))))).trans (cg (fun t => t ◇ (a ◇ c)) (cg (fun t => t ◇ (b ◇ b)) (p1w ((b ◇ b) ◇ (b ◇ c)) (b ◇ b) ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ c))) ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ c))))))).trans (cg (fun t => t ◇ (a ◇ c)) (p2o (b ◇ b) (b ◇ c) ((((b ◇ b) ◇ (b ◇ c)) ◇ (b ◇ b)) ◇ (b ◇ b))))).trans (p1w (a ◇ c) (b ◇ c) ((b ◇ c) ◇ (a ◇ c)) ((b ◇ c) ◇ (a ◇ c)))).symm).trans ((((cg (fun t => t ◇ (a ◇ c)) (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) ((p2t a b c).symm)))).symm).trans (p2x (a ◇ b) (a ◇ c))).trans (((cg (fun t => t ◇ (a ◇ b)) (p1x a b ((a ◇ b) ◇ (a ◇ b)) ((a ◇ b) ◇ (a ◇ b)))).trans (p1w (a ◇ b) (b ◇ b) ((b ◇ b) ◇ (a ◇ b)) ((b ◇ b) ◇ (a ◇ b)))).trans (p2i a b ((a ◇ b) ◇ (b ◇ b)))))
  exact (calc
    x=x:=rfl
    _=(y ◇ (x ◇ ((x ◇ z) ◇ (z ◇ y)))):=((((((cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => (x ◇ z) ◇ t) (p1w y z (z ◇ y) (z ◇ y))))).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (p2y x y z)))).trans (cg (fun t => y ◇ t) (p1w ((x ◇ x) ◇ (x ◇ y)) x (x ◇ ((x ◇ x) ◇ (x ◇ y))) (x ◇ ((x ◇ x) ◇ (x ◇ y)))))).trans (cg (fun t => y ◇ t) (p2s x x y))).trans (p1w ((x ◇ y) ◇ y) y (y ◇ ((x ◇ y) ◇ y)) (y ◇ ((x ◇ y) ◇ y)))).trans (p2p x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6678_to_6681 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6678_to_6681
