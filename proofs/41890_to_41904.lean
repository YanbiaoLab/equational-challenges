-- Equation41890 → Equation41904
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (x ◇ (z ◇ y)))
-- Conclusion: x ◇ y = y ◇ (x ◇ (z ◇ (x ◇ y)))
-- Original submission SHA-256: c5ba7a66d3cb587237a699b07893db395162d1091790720327746637edf24b91
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (x ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (z ◇ (x ◇ y)))
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
    exact ((cg (fun t => (a ◇ b) ◇ t) ((h b b a).symm)).symm).trans ((h b (a ◇ b) b).symm)
  have p1:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a b a)
  have p2:=fun (a b c:G)=>by
    exact ((h a b a).trans (p1 a b a)).symm
  have p3:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (cg (fun t => b ◇ t) ((h c b a).symm))).symm).trans ((h b (c ◇ (a ◇ b)) c).symm)
  have p4:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p0 a b))).symm).trans ((h (a ◇ b) b b).symm)
  have p5:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p0 b b)).trans (p3 a b b)).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p0 a b)).symm).trans (p0 (a ◇ b) (b ◇ b))).trans (cg (fun t => (b ◇ b) ◇ t) (p0 a b)))).symm
  have p6:=fun (a:G)=>by
    exact (((p2 a a (a ◇ (a ◇ (a ◇ (a ◇ a))))).symm).trans (((cg (fun t => a ◇ t) (p5 a a)).symm).trans (p4 a a))).symm
  have p7:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p6 b)))).symm).trans ((h a b (b ◇ b)).symm)
  have p8:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ a)) (p0 a a)).symm).trans (p6 (a ◇ a))).trans (p0 a a)
  have p9:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p0 a b)))).symm).trans ((h c (b ◇ b) (a ◇ b)).symm)
  have pa:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p2 a b a)))).symm).trans (p2 b (a ◇ (a ◇ (a ◇ b))) a)).trans (p2 a b (b ◇ (a ◇ (a ◇ (a ◇ b)))))
  have pb:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ (a ◇ b)))) (p0 b b)).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p5 a b))).symm).trans ((((cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p0 a b))).symm).trans (p5 (a ◇ b) (b ◇ b))).trans ((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p0 a b))).trans (cg (fun t => (b ◇ b) ◇ t) (p5 a b))))
  have pc:=fun (a b:G)=>by
    exact (((cg (fun t => a ◇ t) (p0 (b ◇ a) (b ◇ a))).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => ((b ◇ a) ◇ (b ◇ a)) ◇ t) (p6 (b ◇ a)))).symm).trans ((h ((b ◇ a) ◇ (b ◇ a)) a b).symm))).symm
  have pd:=fun (a b c d:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ (b ◇ d))) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) ((h a d b).symm)))).symm).trans ((h c (a ◇ (a ◇ (b ◇ d))) d).symm)
  have pe:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p3 b b b)).trans (pd b a b b)).symm).trans ((((cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p8 b))).symm).trans (pd b a (b ◇ (b ◇ b)) b)).trans (pb a b))).symm
  have pf:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ (c ◇ (a ◇ b)))) ◇ t) ((h b b a).symm)).symm).trans (pd b c b (a ◇ b))
  have pg:=fun (a b:G)=>by
    exact ((((cg (fun t => (a ◇ b) ◇ t) (pe a b)).trans (p2 b (a ◇ b) ((a ◇ b) ◇ (b ◇ (b ◇ (b ◇ (a ◇ b))))))).symm).trans (((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p5 a b))).symm).trans ((h (b ◇ b) (a ◇ b) b).symm))).symm
  have ph:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (p5 b a)).symm).trans ((((cg (fun t => a ◇ t) (cg (fun t => (a ◇ a) ◇ t) (pg b a))).symm).trans ((h (a ◇ a) a b).symm)).trans (p6 a))
  have pi:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ b) ◇ t) (p5 b (a ◇ b))).trans (p9 a b (a ◇ b))).trans (p0 a b)).symm).trans (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (pg b (a ◇ b)))).symm).trans (p9 a b ((a ◇ b) ◇ (a ◇ b))))).symm
  have pj:=fun (a b:G)=>by
    exact ((((cg (fun t => b ◇ t) (pg b (a ◇ b))).trans (p4 a b)).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (pi a b))).symm).trans ((h ((a ◇ b) ◇ (a ◇ b)) b b).symm))).symm
  have pk:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (a ◇ b))) (p0 b b)).symm).trans ((((cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p0 a b)).symm).trans (pg (a ◇ b) (b ◇ b))).trans ((cg (fun t => (b ◇ b) ◇ t) (p0 a b)).trans (p5 a b)))
  have pl:=fun (a b c:G)=>by
    exact ((((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p5 a c)).trans (pd a b c c)).symm).trans (((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ c) ◇ t) (pg a c))).symm).trans (pd a b (c ◇ c) c))).symm
  have pm:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (pg a b)))).symm).trans ((h c (a ◇ b) (b ◇ b)).symm)
  have pn:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => (b ◇ b) ◇ t) (ph b a))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (p0 b b))).symm).trans ((((cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ (a ◇ b))))) (ph b a))).symm).trans (pc (b ◇ (b ◇ (a ◇ b))) b)).trans (((((((cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ (a ◇ b))))) (ph b a)))).trans (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (ph b a))))).trans (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ t) (p0 b b)))).trans (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ b))) (ph b a)))).trans (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p5 b b))).trans (pd b a b b)).trans (ph b a)))
  have po:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p0 a b))).symm).trans (pl (a ◇ b) b b)).trans ((cg (fun t => b ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p0 a b))).trans (p4 a b))
  have pp:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ b)) (pd a a a b)).symm).trans ((((cg (fun t => ((a ◇ (a ◇ (a ◇ b))) ◇ (a ◇ (a ◇ (a ◇ b)))) ◇ t) (p2 a b a)).symm).trans (pg b (a ◇ (a ◇ (a ◇ b))))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p2 a b (b ◇ (a ◇ (a ◇ (a ◇ b)))))))
  have pq:=fun (a b:G)=>by
    exact (((((((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ (b ◇ (a ◇ b)))) (cg (fun t => b ◇ t) (ph b a)))).trans (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ b))) (ph b a))))).trans (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p5 a b)))).trans (cg (fun t => (a ◇ b) ◇ t) (pn a b))).trans (p0 a b)).symm).trans ((((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (pp b (a ◇ b)))).symm).trans (pm a b (b ◇ (b ◇ (b ◇ (b ◇ (a ◇ b))))))).trans (cg (fun t => t ◇ (a ◇ b)) (cg (fun t => b ◇ t) (ph b a))))).symm
  have pr:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ (a ◇ (b ◇ c))) ◇ (a ◇ (a ◇ (b ◇ c))))) ((h a c b).symm)).symm).trans (p0 c (a ◇ (a ◇ (b ◇ c))))).symm
  have ps:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p2 a b a)).symm).trans (pr a a b)).trans ((cg (fun t => (a ◇ b) ◇ t) (pd a a a b)).trans (p2 a (a ◇ b) ((a ◇ b) ◇ (a ◇ (a ◇ (a ◇ (a ◇ b)))))))
  have pt:=fun (a b:G)=>by
    exact (pp a b).trans (ps a b)
  have pu:=fun (a b:G)=>by
    exact ((((cg (fun t => a ◇ t) (ps b (b ◇ a))).trans (p2 b a (a ◇ (b ◇ (b ◇ (b ◇ a)))))).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ (b ◇ a)))) ◇ t) (pt b a))).symm).trans ((h (b ◇ (b ◇ (b ◇ (b ◇ a)))) a b).symm))).symm
  have pv:=fun (a b c:G)=>by
    exact ((((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (pk a c)).trans (pd a b c c)).symm).trans (((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ (c ◇ c)) ◇ t) (pq a c))).symm).trans (pd a b (c ◇ (c ◇ c)) c))).symm
  have pw:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ (c ◇ (b ◇ (a ◇ b))))) (p0 b b)).symm).trans ((((cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p0 a b)))).symm).trans (pl c (a ◇ b) (b ◇ b))).trans ((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p0 a b)))).trans (p9 a b c)))
  have px:=fun (a b:G)=>by
    exact ((((((((cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p2 a a (a ◇ (a ◇ (a ◇ (a ◇ a)))))))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ a)))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p3 a a a)))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ a)))) (pv a a a))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ a)))) (p2 a a (a ◇ (a ◇ (a ◇ (a ◇ a))))))).trans (pl b a a)).trans (p7 b a)).symm).trans ((((cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (pv a a a)))).symm).trans (pw a (a ◇ (a ◇ a)) b)).trans (cg (fun t => b ◇ t) (p3 a a a)))).symm
  have py:=fun (a b:G)=>by
    exact (((px b (b ◇ (b ◇ (a ◇ b)))).symm).trans (pd b a b b)).trans (ph b a)
  have pz:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ a) ◇ t) (pd a a a a)).trans (cg (fun t => (b ◇ a) ◇ t) (p2 a a (a ◇ (a ◇ (a ◇ (a ◇ a))))))).trans (p0 b a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ (a ◇ a))))) (px a b)).symm).trans (p0 b (a ◇ (a ◇ (a ◇ a))))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (px a b)))).symm
  have p10:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => a ◇ t) (px b a))).symm).trans ((h a (b ◇ (b ◇ b)) b).symm)
  have p11:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ (a ◇ b))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p3 b b b))).trans (cg (fun t => t ◇ (a ◇ (a ◇ b))) (pv b b b))).trans (cg (fun t => t ◇ (a ◇ (a ◇ b))) (p2 b b (b ◇ (b ◇ (b ◇ (b ◇ b))))))).symm).trans ((((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ b)))) ◇ t) (cg (fun t => a ◇ t) (px b a))).symm).trans (pv a b (b ◇ (b ◇ b)))).trans ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => a ◇ t) (px b a))).trans (p10 a b)))
  have p12:=fun (a b:G)=>by
    exact ((((cg (fun t => (a ◇ (a ◇ (b ◇ (a ◇ a)))) ◇ t) (p6 a)).trans (pf a a b)).symm).trans (((cg (fun t => (a ◇ (a ◇ (b ◇ (a ◇ a)))) ◇ t) (po a a)).symm).trans (pd a b (a ◇ a) (a ◇ a)))).symm
  have p13:=fun (a b:G)=>by
    exact ((p12 a b).symm).trans ((h a (a ◇ a) b).symm)
  have p14:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ b)))) (p2 b b (b ◇ (b ◇ (b ◇ (b ◇ b)))))).symm).trans (((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p13 b a)))).symm).trans (pu (b ◇ (a ◇ (b ◇ b))) b))
  have p15:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))) (ph c a)).symm).trans (((cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) ((h a c b).symm))))).symm).trans (pt c (a ◇ (a ◇ (b ◇ c)))))
  have p16:=fun (a b c:G)=>by
    exact (((pg a c).symm).trans (((cg (fun t => (c ◇ c) ◇ t) ((h a c b).symm)).symm).trans (p15 a b c))).symm
  have p17:=fun (a b c:G)=>by
    exact (p15 a b c).trans (p16 a b c)
  have p18:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) (pt a (c ◇ b))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ (a ◇ (c ◇ b))))) ◇ t) (pu (c ◇ b) a))).symm).trans ((h (a ◇ (a ◇ (a ◇ (a ◇ (c ◇ b))))) b c).symm))).symm
  have p19:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ (b ◇ a))) (ph a b)).trans (p11 b a)).symm).trans ((((cg (fun t => t ◇ (b ◇ (b ◇ a))) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p2 b a a))))).symm).trans (p18 a (b ◇ (b ◇ a)) b)).trans ((cg (fun t => (b ◇ (b ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p2 b a (a ◇ (b ◇ (b ◇ (b ◇ a))))))).trans (p3 b a b)))
  have p1a:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ (a ◇ b))) (ph b c)).symm).trans ((((cg (fun t => t ◇ (c ◇ (a ◇ b))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) ((h c b a).symm))))).symm).trans (p18 b (c ◇ (a ◇ b)) c)).trans ((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (p16 c a b)).trans (p3 a b c)))
  have p1b:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (pa a b)))).symm).trans ((h c (b ◇ (b ◇ (a ◇ b))) (a ◇ (a ◇ (a ◇ b)))).symm)
  have p1c:=fun (a b c:G)=>by
    exact ((((((cg (fun t => t ◇ (c ◇ (c ◇ (a ◇ b)))) (ph (b ◇ (b ◇ (a ◇ b))) c)).trans (cg (fun t => t ◇ (c ◇ (c ◇ (a ◇ b)))) (p1b a b b))).trans (cg (fun t => t ◇ (c ◇ (c ◇ (a ◇ b)))) (ph b a))).trans (pl c a b)).symm).trans ((((cg (fun t => t ◇ (c ◇ (c ◇ (a ◇ b)))) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p1b a b c))))).symm).trans (pu (c ◇ (c ◇ (a ◇ b))) (b ◇ (b ◇ (a ◇ b))))).trans (p1b a b c))).symm
  have p1d:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ (a ◇ b))) (ph b a)).trans (p1a a b b)).symm).trans (((cg (fun t => t ◇ (b ◇ (a ◇ b))) (p1b a b b)).symm).trans (pj b (b ◇ (a ◇ b))))).symm
  have p1e:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ a))) ◇ t) (ps b a))).symm).trans ((h (b ◇ (b ◇ (b ◇ a))) a b).symm)
  have p1f:=fun (a b:G)=>by
    exact ((((((cg (fun t => (a ◇ (a ◇ (b ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => b ◇ t) (p7 a b)))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ b))) ◇ t) (p1d a b))).trans (pd a b b b)).trans (p7 a b)).symm).trans ((((cg (fun t => (a ◇ (a ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ (a ◇ (b ◇ b)))))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p7 a b))))).symm).trans (p1e (a ◇ (a ◇ (b ◇ b))) b)).trans ((cg (fun t => t ◇ (a ◇ (a ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p7 a b)))).trans (pd b a a b)))).symm
  have p1g:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (ps a b))).trans (p1e b a)).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p2 a b a)))).symm).trans (p1f b (a ◇ (a ◇ (a ◇ b))))).trans (p2 a b (b ◇ (a ◇ (a ◇ (a ◇ b))))))
  have p1h:=fun (a b:G)=>by
    exact ((((((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => b ◇ t) (p2 a b (b ◇ (a ◇ (a ◇ (a ◇ b)))))))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p1d a b))).trans (pd a a b b)).trans (p2 a b (b ◇ (a ◇ (a ◇ (a ◇ b)))))).symm).trans ((((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ (a ◇ (a ◇ b)))))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p2 a b a))))).symm).trans (p1e (a ◇ (a ◇ (a ◇ b))) b)).trans (cg (fun t => t ◇ (a ◇ (a ◇ (a ◇ b)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p2 a b (b ◇ (a ◇ (a ◇ (a ◇ b)))))))))).symm
  have p1i:=fun (a b:G)=>by
    exact ((((((((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (b ◇ (a ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (p1c a a b)))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (b ◇ (a ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (p7 b a))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (b ◇ a))) (p1c a a b)))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (b ◇ a))) (p7 b a)))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (pz a b)))).trans (po b a)).symm).trans ((((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ (a ◇ a)))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (b ◇ (a ◇ (a ◇ (a ◇ a))))))) (p1h a a)).symm).trans (po b (a ◇ (a ◇ (a ◇ a))))).trans ((cg (fun t => t ◇ (a ◇ (a ◇ (a ◇ a)))) (p1c a a b)).trans (cg (fun t => t ◇ (a ◇ (a ◇ (a ◇ a)))) (p7 b a))))).symm
  have p1j:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ ((a ◇ b) ◇ ((a ◇ b) ◇ b))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p3 b b b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ ((a ◇ b) ◇ b))) (pv b b b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ ((a ◇ b) ◇ b))) (p2 b b (b ◇ (b ◇ (b ◇ (b ◇ b))))))).trans (p1a (a ◇ b) b (a ◇ b))).symm).trans ((((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ b)))) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1i b a))).symm).trans (pv (a ◇ b) b (b ◇ (b ◇ b)))).trans ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1i b a))).trans (p10 (a ◇ b) b)))
  have p1k:=fun (a b c:G)=>by
    exact ((((((cg (fun t => ((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ t) (cg (fun t => c ◇ t) (p1c a a b))).trans (cg (fun t => ((a ◇ (a ◇ (a ◇ a))) ◇ a) ◇ t) (cg (fun t => c ◇ t) (p7 b a)))).trans (cg (fun t => t ◇ (c ◇ (b ◇ a))) (py a a))).trans (p1a b a c)).symm).trans ((((cg (fun t => t ◇ (c ◇ (b ◇ (a ◇ (a ◇ (a ◇ a)))))) (px a (a ◇ (a ◇ (a ◇ a))))).symm).trans (p1a b (a ◇ (a ◇ (a ◇ a))) c)).trans ((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => c ◇ t) (p1c a a b))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => c ◇ t) (p7 b a)))))).symm
  have p1l:=fun (a b c:G)=>by
    exact (((((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ (c ◇ (a ◇ c))) ◇ t) (p16 a b c))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p1d a c))).trans (pd a b c c)).symm).trans ((((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => t ◇ (c ◇ (c ◇ (a ◇ (a ◇ (b ◇ c)))))) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) ((h a c b).symm))))).symm).trans (p1e (a ◇ (a ◇ (b ◇ c))) c)).trans (cg (fun t => t ◇ (a ◇ (a ◇ (b ◇ c)))) (cg (fun t => c ◇ t) (p16 a b c))))).symm
  have p1m:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ c) ◇ t) (cg (fun t => (b ◇ (a ◇ c)) ◇ t) (p3 a c b))).symm).trans ((h (b ◇ (a ◇ c)) (b ◇ c) c).symm)
  have p1n:=fun (a b:G)=>by
    exact (((p17 (b ◇ (a ◇ b)) a b).symm).trans (((cg (fun t => (b ◇ b) ◇ t) (p1c a b (b ◇ (a ◇ b)))).symm).trans (p1m a b b))).symm
  have p1o:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p0 a b))).symm).trans (pv (a ◇ b) b b)).trans ((cg (fun t => b ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p0 a b))).trans (p4 a b))
  have p1p:=fun (a b c:G)=>by
    exact ((((cg (fun t => (c ◇ c) ◇ t) (ps a (c ◇ (b ◇ c)))).trans (p9 b c a)).symm).trans (((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ (c ◇ (b ◇ c))))) ◇ t) (p1g a (c ◇ (b ◇ c))))).symm).trans (p9 b c (a ◇ (a ◇ (a ◇ (c ◇ (b ◇ c)))))))).symm
  have p1q:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p1p a a b)))).symm).trans ((h c (b ◇ b) (a ◇ (a ◇ (a ◇ (b ◇ (a ◇ b)))))).symm)
  have p1r:=fun (a b c:G)=>by
    exact ((((cg (fun t => (c ◇ (c ◇ (a ◇ (b ◇ b)))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p1a b b c))).trans (cg (fun t => (c ◇ (c ◇ (a ◇ (b ◇ b)))) ◇ t) (p14 c b))).trans (pd c a b (b ◇ b))).symm).trans ((((cg (fun t => (c ◇ (c ◇ (a ◇ (b ◇ b)))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p1q a b c)))).symm).trans (p2 (b ◇ b) (c ◇ (c ◇ (a ◇ (b ◇ b)))) a)).trans (p1q a b c))
  have p1s:=fun (a b:G)=>by
    exact (((cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p0 a a)))).trans (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (p19 a b)))).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p6 (a ◇ a))))).symm).trans (p1r ((a ◇ a) ◇ (a ◇ a)) a b))
  have p1t:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => b ◇ t) ((h (a ◇ b) b a).symm))).symm).trans (p1r (a ◇ b) (a ◇ b) b)
  have p1u:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (p1c a b c))).symm).trans (((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p5 a b)))).symm).trans ((h c (b ◇ (a ◇ b)) (b ◇ b)).symm))
  have p1v:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) ((h c b a).symm))).symm).trans (p1u a b c)
  have p1w:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (p1v a b (b ◇ (a ◇ b)))).symm).trans ((h (b ◇ (a ◇ b)) b (b ◇ (a ◇ b))).symm)
  have p1x:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => b ◇ t) (p1w a b))).symm).trans ((h b (b ◇ (a ◇ b)) (b ◇ (a ◇ b))).symm)
  have p1y:=fun (a b c:G)=>by
    exact (((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (px a c)))).symm).trans ((h b (a ◇ (a ◇ (a ◇ a))) c).symm)).trans ((p1c a a b).trans (p7 b a))
  have p1z:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ (b ◇ (b ◇ b))) ◇ t) (p1x a b)).trans (p1l b a b)).trans (ph b a)).symm).trans (((cg (fun t => (b ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p1n a b))).symm).trans (p1y b (b ◇ (a ◇ b)) b))).symm
  have p20:=fun (a b c:G)=>by
    exact ((p1y a (b ◇ (b ◇ (c ◇ a))) b).symm).trans ((((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => (b ◇ (b ◇ (c ◇ a))) ◇ t) (cg (fun t => (b ◇ (b ◇ (c ◇ a))) ◇ t) (p1y a b c)))).symm).trans (p1f (a ◇ (a ◇ (a ◇ a))) (b ◇ (b ◇ (c ◇ a))))).trans (p1y a b c))
  have p21:=fun (a b:G)=>by
    exact ((p1v b a b).symm).trans (((cg (fun t => t ◇ (b ◇ (b ◇ a))) (cg (fun t => a ◇ t) (p2 b a a))).symm).trans (p20 (b ◇ (b ◇ a)) a b))
  have p22:=fun (a b:G)=>by
    exact (p1n a b).trans (cg (fun t => b ◇ t) (p1z a b))
  have p23:=fun (a b:G)=>by
    exact ((((((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p3 a b b)))).trans (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pl b a b)))).trans (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (ph b a)))).trans (cg (fun t => (b ◇ b) ◇ t) (p22 a b))).trans (p1a b b b)).symm).trans ((((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p22 a b))))).symm).trans (p1s (b ◇ b) (b ◇ (a ◇ b)))).trans ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p0 b b)).trans (p3 a b b)))
  have p24:=fun (a b c:G)=>by
    exact (((p23 a c).symm).trans (p23 b c)).symm
  have p25:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p24 a b c)).symm).trans (p1f b c)
  have p26:=fun (a b c:G)=>by
    exact ((((((cg (fun t => c ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p25 a (b ◇ (a ◇ b)) b))).trans (cg (fun t => c ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p1z a b)))).trans (cg (fun t => c ◇ t) (p22 a b))).trans (p19 b c)).symm).trans (((cg (fun t => c ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pk a b)))).symm).trans (p25 (b ◇ (b ◇ b)) c (b ◇ (a ◇ b))))).symm
  have p27:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ a) ◇ t) (pz a (b ◇ a))).trans (p1t b a)).symm).trans ((((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (p1i a b))).symm).trans (p21 (a ◇ (a ◇ (a ◇ a))) (b ◇ a))).trans (((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p25 a (b ◇ a) a))).trans (p1k a (b ◇ a) (b ◇ a))).trans (p1j b a)))
  have p28:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) (p1a a a b)).symm).trans (p26 b (a ◇ a) c)).trans ((pl c a a).trans (p7 c a))
  have p29:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p1z a b)))).trans (cg (fun t => t ◇ (a ◇ b)) (cg (fun t => b ◇ t) (p22 a b)))).trans (pz b a)).symm).trans (((cg (fun t => t ◇ (a ◇ b)) (p26 a b (b ◇ (a ◇ b)))).symm).trans (pj b (a ◇ b)))).symm
  have p2a:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (cg (fun t => b ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p1z a b)))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (cg (fun t => b ◇ t) (p22 a b)))).trans (p1k b a (a ◇ b))).trans (p27 b a)).symm).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (p26 a b (b ◇ (a ◇ b)))).symm).trans (pi b (a ◇ b)))
  have p2b:=fun (a b:G)=>by
    exact ((((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ (b ◇ (a ◇ b)))) ◇ t) (p3 b b b)).trans (cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ b)))) (p1o a b))).trans (p25 b ((a ◇ b) ◇ b) b)).symm).trans ((((cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ b)))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p2a a b))).symm).trans (p22 (a ◇ b) (b ◇ (b ◇ b)))).trans (((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p3 b b b)).trans (pv b b b)).trans (p2 b b (b ◇ (b ◇ (b ◇ (b ◇ b)))))))
  have p2c:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ b)) (p29 a b)).trans (p29 a b)).symm).trans (((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => t ◇ (a ◇ b)) (pg a b))).symm).trans (p2b (b ◇ b) (a ◇ b)))).symm
  have p2d:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ a) (p25 a (b ◇ a) (b ◇ a))).trans (cg (fun t => t ◇ a) (p2c b a))).trans (p1z b a)).symm).trans ((((cg (fun t => t ◇ a) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p2c b a))))).symm).trans (p18 (b ◇ a) a b)).trans ((((cg (fun t => a ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p2c b a))).trans (p26 a (b ◇ a) a)).trans (cg (fun t => (b ◇ a) ◇ t) (p26 b a a))).trans (p25 a (b ◇ a) a)))).symm
  have p2e:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ b) ◇ t) (p2 a b (b ◇ (a ◇ (a ◇ (a ◇ b)))))).trans (p2c a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ (a ◇ b))))) (p2 a b a)).symm).trans (p2c b (a ◇ (a ◇ (a ◇ b))))).trans ((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p2 a b (b ◇ (a ◇ (a ◇ (a ◇ b)))))).trans (ps a b)))
  have p2f:=fun (a b:G)=>by
    exact ((((cg (fun t => b ◇ t) (p28 b (a ◇ b) (a ◇ b))).trans (cg (fun t => b ◇ t) (p2d b a))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p2d b a))))).symm).trans (p1s b (a ◇ b)))).symm
  have p2g:=fun (a b:G)=>by
    exact ((p2f a b).symm).trans ((p0 a b).trans (p2e a b))
  have p2h:=fun (a b:G)=>by
    exact (((p7 a b).symm).trans ((((cg (fun t => b ◇ t) (p2g a (b ◇ b))).symm).trans (p7 (b ◇ b) b)).trans (p2d b b))).symm
  have p2i:=fun (a b c:G)=>by
    exact (((p2h a c).symm).trans (p2h b c)).symm
  have p2j:=fun (a b:G)=>by
    exact ((((((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p2f b b)))).trans (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p1a b b b)))).trans (cg (fun t => b ◇ t) (p28 b b a))).trans (p2e a b)).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) ((p2g a (b ◇ b)).symm))).symm).trans (p1r a b a))).symm
  have p2k:=fun (a b c:G)=>by
    exact (((p2g a c).symm).trans (p2g b c)).symm
  have p2l:=fun (a b:G)=>by
    exact (((cg (fun t => a ◇ t) (p28 a a b)).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) ((p2g b a).symm)))).symm).trans (p1s a b))).symm
  have p2m:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) (p2h a c)).symm).trans (p2j b c)).symm
  have p2n:=fun (a b:G)=>by
    exact (((cg (fun t => a ◇ t) (p2d a a)).symm).trans ((((p2l a (a ◇ a)).symm).trans (p2h b (a ◇ a))).trans (p2l a b))).symm
  have p2o:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) (p2h a b)).symm).trans (p2l b c)).trans (p2n b c)
  have p2p:=fun (a b c:G)=>by
    exact (((p2i a c (b ◇ c)).symm).trans (p2e b c)).symm
  have p2q:=fun (a b c d:G)=>by
    exact (((cg (fun t => c ◇ t) (p2i a c d)).symm).trans (p2m b c d)).symm
  have p2r:=fun (a b c d:G)=>by
    exact ((p2q a c c d).symm).trans (p2k b c d)
  have p2s:=fun (a b c d:G)=>by
    exact ((p2q a c c d).symm).trans (p2p b c d)
  have p2t:=fun (a b:G)=>by
    exact (((p2e a (a ◇ b)).symm).trans ((((cg (fun t => (a ◇ b) ◇ t) (p2e a b)).symm).trans (p2e b (a ◇ b))).trans (cg (fun t => b ◇ t) (p2e a b)))).symm
  have p2u:=fun (a b c d e:G)=>by
    exact (((p2i a c (c ◇ e)).symm).trans ((p2r b c d e).symm)).symm
  have p2v:=fun (a b c:G)=>by
    exact (((p2t a c).symm).trans (((cg (fun t => c ◇ t) (p2e a c)).symm).trans (p2k b c (a ◇ c)))).symm
  have p2w:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) ((p2g a b).symm)).symm).trans (p2v a a b)
  have p2x:=fun (a b c d:G)=>by
    exact ((cg (fun t => c ◇ t) ((p2s a c b d).symm)).symm).trans (p2v b c d)
  have p2y:=fun (a b c d e:G)=>by
    exact ((p2u a c b d (c ◇ (e ◇ d))).symm).trans ((h c d e).symm)
  exact (calc
    (x ◇ y)=(x ◇ y):=rfl
    _=(y ◇ (x ◇ (z ◇ (x ◇ y)))):=((((cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (p2o x y z))).trans (cg (fun t => y ◇ t) (p2w x y))).trans (p2x x x y (x ◇ y))).trans (p2y x x x y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41890_to_41904 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41890_to_41904
