-- Equation13669 → Equation13823
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ y)
-- Conclusion: x = y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ y)
-- Original submission SHA-256: 330b3186d380dbc7d033dc19868cf16747cfc56e2c25b17e0db8bd2e09896a79
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((y ◇ ((x ◇ x) ◇ y)) ◇ y)
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

def cub (a : CM) : CM := p (p a a) a

def q (a : CM) : CM := p a (cub a)

def lhs0 (a x : CM) : CM := p a (p (q x) a)

def lhs1 (a b : CM) : CM := p (p (q a) (q b)) a

def get0a : CM → CM
  | p a _ => a
  | _ => e

def get0x : CM → CM
  | p _ (p (p x _) _) => x
  | _ => e

def get1a : CM → CM
  | p _ a => a
  | _ => e

def get1b : CM → CM
  | p (p _ (p b _)) _ => b
  | _ => e

def root (t : CM) : CM :=
  let a0 := get0a t
  let x0 := get0x t
  if t = lhs0 a0 x0 then
    x0
  else
    let a1 := get1a t
    let b1 := get1b t
    if t = lhs1 a1 b1 then b1 else t

def op (a b : CM) : CM := root (p a b)

instance instMagma : Magma CM where
  op := op

theorem lhs1_ne_lhs0 (a b x : CM) :
    lhs1 a b = lhs0 (p (q a) (q b)) x → False := by
  intro h
  have hs := congrArg sz h
  simp [lhs0, lhs1, q, cub, sz] at hs
  omega

theorem root_lhs0 (a x : CM) : root (lhs0 a x) = x := by
  change
    (if lhs0 a x = lhs0 a x then x
      else
        if lhs0 a x =
            lhs1 (get1a (lhs0 a x)) (get1b (lhs0 a x))
          then get1b (lhs0 a x) else lhs0 a x) = x
  rw [if_pos rfl]

theorem root_lhs1 (a b : CM) : root (lhs1 a b) = b := by
  change
    (if lhs1 a b =
        lhs0 (p (q a) (q b)) (get0x (lhs1 a b))
      then get0x (lhs1 a b)
      else if lhs1 a b = lhs1 a b then b else lhs1 a b) = b
  rw [if_neg (lhs1_ne_lhs0 a b _), if_pos rfl]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0a t) (get0x t) → False)
    (h1 : t = lhs1 (get1a t) (get1b t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1]

theorem op_rule0 (a x : CM) : op a (p (q x) a) = x := by
  exact root_lhs0 a x

theorem op_rule1 (a b : CM) : op (p (q a) (q b)) a = b := by
  exact root_lhs1 a b

theorem no_yy_lhs0 (y a x : CM) :
    p y y = lhs0 a x → False := by
  intro h
  have hleft : y = a := (CM.p.inj h).1
  have hright : y = p (q x) a := (CM.p.inj h).2
  have hself : y = p (q x) y :=
    hright.trans (congrArg (fun t => p (q x) t) hleft.symm)
  have hs := congrArg sz hself
  simp [q, cub, sz] at hs
  omega

theorem no_yy_lhs1 (y a b : CM) :
    p y y = lhs1 a b → False := by
  intro h
  have hleft : y = p (q a) (q b) := (CM.p.inj h).1
  have hright : y = a := (CM.p.inj h).2
  have hself : y = p (q y) (q b) :=
    hleft.trans (congrArg (fun t => p (q t) (q b)) hright.symm)
  have hs := congrArg sz hself
  simp [q, cub, sz] at hs
  omega

theorem op_yy_raw (y : CM) : op y y = p y y := by
  unfold op
  apply root_eq_self
  · exact no_yy_lhs0 y _ _
  · exact no_yy_lhs1 y _ _

theorem no_cub_lhs0 (y a x : CM) :
    cub y = lhs0 a x → False := by
  intro h
  have hleft : p y y = a := (CM.p.inj h).1
  have hright : y = p (q x) a := (CM.p.inj h).2
  have hlarge : y = p (q x) (p y y) :=
    hright.trans (congrArg (fun t => p (q x) t) hleft.symm)
  have hs := congrArg sz hlarge
  simp [q, cub, sz] at hs
  omega

theorem no_cub_lhs1 (y a b : CM) :
    cub y = lhs1 a b → False := by
  intro h
  have hleft : p y y = p (q a) (q b) := (CM.p.inj h).1
  have hright : y = a := (CM.p.inj h).2
  have hhead : y = q a := (CM.p.inj hleft).1
  have hself : y = q y := hhead.trans (congrArg q hright.symm)
  have hs := congrArg sz hself
  simp [q, cub, sz] at hs
  omega

theorem op_cub_raw (y : CM) : op (p y y) y = cub y := by
  change root (cub y) = cub y
  apply root_eq_self
  · exact no_cub_lhs0 y _ _
  · exact no_cub_lhs1 y _ _

theorem no_q_lhs0 (y a x : CM) :
    q y = lhs0 a x → False := by
  intro h
  have hleft : y = a := (CM.p.inj h).1
  have hright : cub y = p (q x) a := (CM.p.inj h).2
  have hright' : cub y = p (q x) y :=
    hright.trans (congrArg (fun t => p (q x) t) hleft.symm)
  have hhead : p y y = q x := (CM.p.inj hright').1
  have hx1 : y = x := (CM.p.inj hhead).1
  have hx2 : y = cub x := (CM.p.inj hhead).2
  have hself : x = cub x := hx1.symm.trans hx2
  have hs := congrArg sz hself
  simp [cub, sz] at hs
  omega

theorem no_q_lhs1 (y a b : CM) :
    q y = lhs1 a b → False := by
  intro h
  have hleft : y = p (q a) (q b) := (CM.p.inj h).1
  have hright : cub y = a := (CM.p.inj h).2
  have hself : y = p (q (cub y)) (q b) :=
    hleft.trans (congrArg (fun t => p (q t) (q b)) hright.symm)
  have hs := congrArg sz hself
  simp [q, cub, sz] at hs
  omega

theorem op_q_raw (y : CM) : op y (cub y) = q y := by
  change root (q y) = q y
  apply root_eq_self
  · exact no_q_lhs0 y _ _
  · exact no_q_lhs1 y _ _

theorem mid_ne_lhs1 (x y a b : CM) :
    p (q x) y = lhs1 a b → False := by
  intro h
  have hleft : q x = p (q a) (q b) := (CM.p.inj h).1
  have htail : cub x = q b := (CM.p.inj hleft).2
  have hb : p x x = b := (CM.p.inj htail).1
  have hx : x = cub b := (CM.p.inj htail).2
  have hself : x = cub (p x x) :=
    hx.trans (congrArg cub hb.symm)
  have hs := congrArg sz hself
  simp [cub, sz] at hs
  omega

theorem source_holds (x y : CM) :
    x = op y (op (op x (op (op x x) x)) y) := by
  rw [op_yy_raw, op_cub_raw, op_q_raw]
  let u := get0x (p (q x) y)
  by_cases hm : p (q x) y = lhs0 (q x) u
  · have hy : y = p (q u) (q x) := (CM.p.inj hm).2
    have hmid : op (q x) y = u := by
      unfold op
      change root (p (q x) y) = u
      unfold root
      change
        (if p (q x) y = lhs0 (q x) u then u
          else
            if p (q x) y =
                lhs1 (get1a (p (q x) y)) (get1b (p (q x) y))
              then get1b (p (q x) y) else p (q x) y) = u
      rw [if_pos hm]
    rw [hmid, hy]
    exact (op_rule1 u x).symm
  · have hmid : op (q x) y = p (q x) y := by
      unfold op
      apply root_eq_self
      · exact hm
      · exact mid_ne_lhs1 x y _ _
    rw [hmid]
    exact (op_rule0 y x).symm

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e (CM.p CM.e CM.e)
    change
      CM.e =
        CM.p
          (CM.p CM.e CM.e)
          (CM.p
            (CM.p
              (CM.p CM.e CM.e)
              (CM.p
                (CM.p CM.e CM.e)
                (CM.p CM.e CM.e)))
            (CM.p CM.e CM.e)) at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_13669_to_13823 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_13669_to_13823
