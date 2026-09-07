-- Equation30727 → Equation60396
-- Recorded verdict: false
-- Premise: x = (y ◇ (z ◇ ((y ◇ y) ◇ x))) ◇ x
-- Conclusion: (x ◇ y) ◇ y = (z ◇ y) ◇ (y ◇ y)
-- Original submission SHA-256: 3fa5bc189e09c1628366ad31f519ed67e88e31509dd5e565b2e8b7a25e8ba0f6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ ((y ◇ y) ◇ x))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (z ◇ y) ◇ (y ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   

set_option maxRecDepth 10000

namespace submission

inductive CM where
  | e : CM
  | p : CM → CM → CM
deriving DecidableEq

namespace CM

def sz : CM → Nat
  | e => 0
  | p a b => sz a + sz b + 1

def sq (a : CM) : CM := p a a
def q (y x : CM) : CM := p (sq y) x

def lhs0 (y z x : CM) : CM :=
  p (p y (p z (q y x))) x

def lhs1 (y x : CM) : CM :=
  p (p y (q y x)) x

def get0y : CM → CM
  | p (p y _) _ => y
  | _ => e

def get0z : CM → CM
  | p (p _ (p z _)) _ => z
  | _ => e

def get0x : CM → CM
  | p _ x => x
  | _ => e

def get1y : CM → CM
  | p (p y _) _ => y
  | _ => e

def get1x : CM → CM
  | p _ x => x
  | _ => e

def root (t : CM) : CM :=
  let y0 := get0y t
  let z0 := get0z t
  let x0 := get0x t
  if t = lhs0 y0 z0 x0 then
    x0
  else
    let y1 := get1y t
    let x1 := get1x t
    if t = lhs1 y1 x1 then x1 else t

def op (a b : CM) : CM := root (p a b)

instance instMagma : Magma CM where
  op := op

theorem lhs1_ne_lhs0 (y x : CM) :
    lhs1 y x = lhs0 y (sq y) x → False := by
  intro h
  have hright :
      q y x = p (sq y) (q y x) :=
    (CM.p.inj (CM.p.inj h).1).2
  have hs := congrArg sz hright
  simp [q, sq, sz] at hs
  omega

theorem root_lhs0 (y z x : CM) : root (lhs0 y z x) = x := by
  change
    (if lhs0 y z x = lhs0 y z x then x
      else
        if lhs0 y z x =
            lhs1 (get1y (lhs0 y z x)) (get1x (lhs0 y z x))
        then get1x (lhs0 y z x) else lhs0 y z x) = x
  rw [if_pos rfl]

theorem root_lhs1 (y x : CM) : root (lhs1 y x) = x := by
  change
    (if lhs1 y x = lhs0 y (sq y) x then x
      else if lhs1 y x = lhs1 y x then x else lhs1 y x) = x
  rw [if_neg (lhs1_ne_lhs0 y x), if_pos rfl]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0y t) (get0z t) (get0x t) → False)
    (h1 : t = lhs1 (get1y t) (get1x t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1]

theorem op_rule0 (y z x : CM) :
    op (p y (p z (q y x))) x = x := by
  exact root_lhs0 y z x

theorem op_rule1 (y x : CM) :
    op (p y (q y x)) x = x := by
  exact root_lhs1 y x

theorem no_yy_lhs0 (y a z x : CM) :
    p y y = lhs0 a z x → False := by
  intro h
  have hleft : y = p a (p z (q a x)) := (CM.p.inj h).1
  have hright : y = x := (CM.p.inj h).2
  have hself : x = p a (p z (q a x)) := hright.symm.trans hleft
  have hs := congrArg sz hself
  simp [q, sq, sz] at hs
  omega

theorem no_yy_lhs1 (y a x : CM) :
    p y y = lhs1 a x → False := by
  intro h
  have hleft : y = p a (q a x) := (CM.p.inj h).1
  have hright : y = x := (CM.p.inj h).2
  have hself : x = p a (q a x) := hright.symm.trans hleft
  have hs := congrArg sz hself
  simp [q, sq, sz] at hs
  omega

theorem op_yy_raw (y : CM) : op y y = p y y := by
  unfold op
  apply root_eq_self
  · exact no_yy_lhs0 y _ _ _
  · exact no_yy_lhs1 y _ _

theorem no_q_lhs0 (y x a z b : CM) :
    q y x = lhs0 a z b → False := by
  intro h
  have hleft : sq y = p a (p z (q a b)) := (CM.p.inj h).1
  have hright : x = b := (CM.p.inj h).2
  have hy : y = a := (CM.p.inj hleft).1
  have hcycle : y = p z (q y x) := by
    have htail : y = p z (q a b) := (CM.p.inj hleft).2
    simpa [hy, hright] using htail
  have hs := congrArg sz hcycle
  simp [q, sq, sz] at hs
  omega

theorem no_q_lhs1 (y x a b : CM) :
    q y x = lhs1 a b → False := by
  intro h
  have hleft : sq y = p a (q a b) := (CM.p.inj h).1
  have hright : x = b := (CM.p.inj h).2
  have hy : y = a := (CM.p.inj hleft).1
  have hcycle : y = q y x := by
    have htail : y = q a b := (CM.p.inj hleft).2
    simpa [hy, hright] using htail
  have hs := congrArg sz hcycle
  simp [q, sq, sz] at hs
  omega

theorem op_q_raw (y x : CM) : op (sq y) x = q y x := by
  unfold op
  apply root_eq_self
  · exact no_q_lhs0 y x _ _ _
  · exact no_q_lhs1 y x _ _

theorem no_y_q_lhs0 (y x a z b : CM) :
    p y (q y x) = lhs0 a z b → False := by
  intro h
  have hleft : y = p a (p z (q a b)) := (CM.p.inj h).1
  have hright : q y x = b := (CM.p.inj h).2
  have hcycle : y = p a (p z (q a (q y x))) := by
    simpa [hright] using hleft
  have hs := congrArg sz hcycle
  simp [q, sq, sz] at hs
  omega

theorem no_y_q_lhs1 (y x a b : CM) :
    p y (q y x) = lhs1 a b → False := by
  intro h
  have hleft : y = p a (q a b) := (CM.p.inj h).1
  have hright : q y x = b := (CM.p.inj h).2
  have hcycle : y = p a (q a (q y x)) := by
    simpa [hright] using hleft
  have hs := congrArg sz hcycle
  simp [q, sq, sz] at hs
  omega

theorem op_y_q_raw (y x : CM) :
    op y (q y x) = p y (q y x) := by
  unfold op
  apply root_eq_self
  · exact no_y_q_lhs0 y x _ _ _
  · exact no_y_q_lhs1 y x _ _

theorem no_y_z_q_lhs0 (y z x a c b : CM) :
    p y (p z (q y x)) = lhs0 a c b → False := by
  intro h
  have hleft : y = p a (p c (q a b)) := (CM.p.inj h).1
  have hright : p z (q y x) = b := (CM.p.inj h).2
  have hcycle : y = p a (p c (q a (p z (q y x)))) := by
    simpa [hright] using hleft
  have hs := congrArg sz hcycle
  simp [q, sq, sz] at hs
  omega

theorem no_y_z_q_lhs1 (y z x a b : CM) :
    p y (p z (q y x)) = lhs1 a b → False := by
  intro h
  have hleft : y = p a (q a b) := (CM.p.inj h).1
  have hright : p z (q y x) = b := (CM.p.inj h).2
  have hcycle : y = p a (q a (p z (q y x))) := by
    simpa [hright] using hleft
  have hs := congrArg sz hcycle
  simp [q, sq, sz] at hs
  omega

theorem op_y_z_q_raw (y z x : CM) :
    op y (p z (q y x)) = p y (p z (q y x)) := by
  unfold op
  apply root_eq_self
  · exact no_y_z_q_lhs0 y z x _ _ _
  · exact no_y_z_q_lhs1 y z x _ _

theorem source_holds (x y z : CM) :
    x = op (op y (op z (op (op y y) x))) x := by
  rw [op_yy_raw]
  change x = op (op y (op z (op (sq y) x))) x
  rw [op_q_raw]
  let t := p z (q y x)
  by_cases h0 :
      t = lhs0 (get0y t) (get0z t) (get0x t)
  · have hx : get0x t = q y x := by
      exact (CM.p.inj h0).2.symm
    have ht : op z (q y x) = q y x := by
      change root t = q y x
      rw [h0, root_lhs0, hx]
    rw [ht, op_y_q_raw]
    exact (op_rule1 y x).symm
  · by_cases h1 : t = lhs1 (get1y t) (get1x t)
    · have hx : get1x t = q y x := by
        exact (CM.p.inj h1).2.symm
      have ht : op z (q y x) = q y x := by
        change root t = q y x
        unfold root
        rw [if_neg h0, if_pos h1, hx]
      rw [ht, op_y_q_raw]
      exact (op_rule1 y x).symm
    · have ht : op z (q y x) = t := by
        change root t = t
        exact root_eq_self h0 h1
      rw [ht, op_y_z_q_raw]
      exact (op_rule0 y z x).symm

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y z
    exact CM.source_holds x y z
  · intro target
    have bad := target CM.e CM.e CM.e
    change
      CM.op (CM.op CM.e CM.e) CM.e =
        CM.op (CM.op CM.e CM.e) (CM.op CM.e CM.e) at bad
    rw [CM.op_yy_raw] at bad
    change
      CM.op (CM.sq CM.e) CM.e =
        CM.op (CM.sq CM.e) (CM.sq CM.e) at bad
    rw [CM.op_q_raw, CM.op_q_raw] at bad
    exact CM.noConfusion (CM.p.inj bad).2

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30727_to_60396 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_30727_to_60396
