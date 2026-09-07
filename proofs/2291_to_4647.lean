-- Equation2291 → Equation4647
-- Recorded verdict: false
-- Premise: x = (y ◇ (x ◇ (x ◇ x))) ◇ y
-- Conclusion: (x ◇ y) ◇ x = (z ◇ y) ◇ z
-- Original submission SHA-256: c850496023e200f2119904cfca0c50e5330b77c827d472ef5eb801118891ff9d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (x ◇ (x ◇ x))) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (z ◇ y) ◇ z
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
def cub (a : CM) : CM := p a (sq a)

def lhs0 (y x : CM) : CM :=
  p (p y (cub x)) y

def lhs1 (a b : CM) : CM :=
  p a (p (cub b) (cub a))

def get0y : CM → CM
  | p _ y => y
  | _ => e

def get0x : CM → CM
  | p (p _ (p x _)) _ => x
  | _ => e

def get1a : CM → CM
  | p a _ => a
  | _ => e

def get1b : CM → CM
  | p _ (p (p b _) _) => b
  | _ => e

def root (t : CM) : CM :=
  let y0 := get0y t
  let x0 := get0x t
  if t = lhs0 y0 x0 then
    x0
  else
    let a1 := get1a t
    let b1 := get1b t
    if t = lhs1 a1 b1 then b1 else t

def op (a b : CM) : CM := root (p a b)

instance instMagma : Magma CM where
  op := op

theorem lhs1_ne_lhs0 (a b x : CM) :
    lhs1 a b = lhs0 (p (cub b) (cub a)) x → False := by
  intro h
  have hleft :
      a = p (p (cub b) (cub a)) (cub x) :=
    (CM.p.inj h).1
  have hs := congrArg sz hleft
  simp [cub, sq, sz] at hs
  omega

theorem root_lhs0 (y x : CM) : root (lhs0 y x) = x := by
  change
    (if lhs0 y x = lhs0 y x then x
      else
        if lhs0 y x =
            lhs1 (get1a (lhs0 y x)) (get1b (lhs0 y x))
        then get1b (lhs0 y x) else lhs0 y x) = x
  rw [if_pos rfl]

theorem root_lhs1 (a b : CM) : root (lhs1 a b) = b := by
  change
    (if lhs1 a b =
          lhs0 (p (cub b) (cub a)) (get0x (lhs1 a b))
      then get0x (lhs1 a b)
      else if lhs1 a b = lhs1 a b then b else lhs1 a b) = b
  rw [if_neg (lhs1_ne_lhs0 a b _), if_pos rfl]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0y t) (get0x t) → False)
    (h1 : t = lhs1 (get1a t) (get1b t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1]

theorem op_rule0 (y x : CM) :
    op (p y (cub x)) y = x := by
  exact root_lhs0 y x

theorem op_rule1 (a b : CM) :
    op a (p (cub b) (cub a)) = b := by
  exact root_lhs1 a b

theorem no_yy_lhs0 (y a x : CM) :
    p y y = lhs0 a x → False := by
  intro h
  have hleft : y = p a (cub x) := (CM.p.inj h).1
  have hright : y = a := (CM.p.inj h).2
  have hself : a = p a (cub x) := hright.symm.trans hleft
  have hs := congrArg sz hself
  simp [cub, sq, sz] at hs
  omega

theorem no_yy_lhs1 (y a b : CM) :
    p y y = lhs1 a b → False := by
  intro h
  have hleft : y = a := (CM.p.inj h).1
  have hright : y = p (cub b) (cub a) := (CM.p.inj h).2
  have hself : a = p (cub b) (cub a) := hleft.symm.trans hright
  have hs := congrArg sz hself
  simp [cub, sq, sz] at hs
  omega

theorem op_yy_raw (y : CM) : op y y = p y y := by
  unfold op
  apply root_eq_self
  · exact no_yy_lhs0 y _ _
  · exact no_yy_lhs1 y _ _

theorem no_cub_lhs0 (x a b : CM) :
    cub x = lhs0 a b → False := by
  intro h
  have hleft : x = p a (cub b) := (CM.p.inj h).1
  have hright : sq x = a := (CM.p.inj h).2
  have hcycle : x = p (sq x) (cub b) := by
    simpa [hright] using hleft
  have hs := congrArg sz hcycle
  simp [cub, sq, sz] at hs
  omega

theorem no_cub_lhs1 (x a b : CM) :
    cub x = lhs1 a b → False := by
  intro h
  have hleft : x = a := (CM.p.inj h).1
  have hright : sq x = p (cub b) (cub a) := (CM.p.inj h).2
  have hcycle : sq x = p (cub b) (cub x) := by
    simpa [hleft] using hright
  have hs := congrArg sz hcycle
  simp [cub, sq, sz] at hs
  omega

theorem op_x_xx_raw (x : CM) :
    op x (sq x) = cub x := by
  change root (cub x) = cub x
  apply root_eq_self
  · exact no_cub_lhs0 x _ _
  · exact no_cub_lhs1 x _ _

theorem mid_ne_lhs1 (x y a b : CM) :
    p y (cub x) = lhs1 a b → False := by
  intro h
  have hy : y = a := (CM.p.inj h).1
  have hright : cub x = p (cub b) (cub a) := (CM.p.inj h).2
  have hx : x = cub b := (CM.p.inj hright).1
  have hsquare : sq x = cub a := (CM.p.inj hright).2
  have hself : sq (cub b) = cub y := by
    simpa [hx, hy] using hsquare
  have hleft : cub b = y := (CM.p.inj hself).1
  have htail : cub b = sq y := (CM.p.inj hself).2
  have hcycle : y = sq y := hleft.symm.trans htail
  have hs := congrArg sz hcycle
  simp [sq, sz] at hs
  omega

theorem source_holds (x y : CM) :
    x = op (op y (op x (op x x))) y := by
  rw [op_yy_raw]
  change x = op (op y (op x (sq x))) y
  rw [op_x_xx_raw]
  let t := p y (cub x)
  by_cases h0 : t = lhs0 (get0y t) (get0x t)
  · have ha : cub x = get0y t := by
      exact (CM.p.inj h0).2.symm
    have hy :
        y = p (cub x) (cub (get0x t)) := by
      have hleft : y = p (get0y t) (cub (get0x t)) :=
        (CM.p.inj h0).1
      simpa [ha] using hleft
    have ht : op y (cub x) = get0x t := by
      change root t = get0x t
      unfold root
      rw [if_pos h0]
    rw [ht, hy]
    exact (op_rule1 (get0x t) x).symm
  · have ht : op y (cub x) = t := by
      change root t = t
      apply root_eq_self h0
      exact mid_ne_lhs1 x y _ _
    rw [ht]
    exact (op_rule0 y x).symm

theorem witness_inner :
    op (sq e) e = p (sq e) e := by
  rfl

theorem witness_outer :
    op (p (sq e) e) (sq e) =
      p (p (sq e) e) (sq e) := by
  rfl

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e CM.e (CM.sq CM.e)
    change
      CM.op (CM.op CM.e CM.e) CM.e =
        CM.op (CM.op (CM.sq CM.e) CM.e) (CM.sq CM.e) at bad
    rw [CM.op_yy_raw] at bad
    change
      CM.op (CM.sq CM.e) CM.e =
        CM.op (CM.op (CM.sq CM.e) CM.e) (CM.sq CM.e) at bad
    rw [CM.witness_inner, CM.witness_outer] at bad
    exact CM.noConfusion (CM.p.inj (CM.p.inj bad).1).1

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2291_to_4647 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2291_to_4647
