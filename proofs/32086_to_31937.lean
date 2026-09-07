-- Equation32086 → Equation31937
-- Recorded verdict: false
-- Premise: x = (y ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ y
-- Conclusion: x = (x ◇ ((y ◇ (x ◇ x)) ◇ y)) ◇ x
-- Original submission SHA-256: 5c4ffe67cdf7aa6da43fed167ef00c13eedb323d6e5914cdd904785244dea120
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ ((y ◇ (x ◇ x)) ◇ y)) ◇ x
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

def tri (a : CM) : CM := p a (p a a)

def q (a : CM) : CM := p (tri a) a

def lhs0 (a x : CM) : CM := p (p a (q x)) a

def lhs1 (a b : CM) : CM := p a (p (q b) (q a))

def get0a : CM → CM
  | p _ a => a
  | _ => e

def get0x : CM → CM
  | p (p _ (p (p x _) _)) _ => x
  | _ => e

def get1a : CM → CM
  | p a _ => a
  | _ => e

def get1b : CM → CM
  | p _ (p (p (p b _) _) _) => b
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
    lhs1 a b = lhs0 (p (q b) (q a)) x → False := by
  intro h
  have hs := congrArg sz h
  simp [lhs0, lhs1, q, tri, sz] at hs
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
        lhs0 (p (q b) (q a)) (get0x (lhs1 a b))
      then get0x (lhs1 a b)
      else if lhs1 a b = lhs1 a b then b else lhs1 a b) = b
  rw [if_neg (lhs1_ne_lhs0 a b _), if_pos rfl]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0a t) (get0x t) → False)
    (h1 : t = lhs1 (get1a t) (get1b t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1]

theorem op_rule0 (a x : CM) : op (p a (q x)) a = x := by
  exact root_lhs0 a x

theorem op_rule1 (a b : CM) : op a (p (q b) (q a)) = b := by
  exact root_lhs1 a b

theorem no_yy_lhs0 (y a x : CM) :
    p y y = lhs0 a x → False := by
  intro h
  have hleft : y = p a (q x) := (CM.p.inj h).1
  have hright : y = a := (CM.p.inj h).2
  have hself : a = p a (q x) := hright.symm.trans hleft
  have hs := congrArg sz hself
  simp [q, tri, sz] at hs
  omega

theorem no_yy_lhs1 (y a b : CM) :
    p y y = lhs1 a b → False := by
  intro h
  have hleft : y = a := (CM.p.inj h).1
  have hright : y = p (q b) (q a) := (CM.p.inj h).2
  have hself : y = p (q b) (q y) :=
    hright.trans (congrArg (fun t => p (q b) (q t)) hleft.symm)
  have hs := congrArg sz hself
  simp [q, tri, sz] at hs
  omega

theorem op_yy_raw (y : CM) : op y y = p y y := by
  unfold op
  apply root_eq_self
  · exact no_yy_lhs0 y _ _
  · exact no_yy_lhs1 y _ _

theorem no_tri_lhs0 (y a x : CM) :
    tri y = lhs0 a x → False := by
  intro h
  have hleft : y = p a (q x) := (CM.p.inj h).1
  have hright : p y y = a := (CM.p.inj h).2
  have hlarge : y = p (p y y) (q x) :=
    hleft.trans (congrArg (fun t => p t (q x)) hright.symm)
  have hs := congrArg sz hlarge
  simp [q, tri, sz] at hs
  omega

theorem no_tri_lhs1 (y a b : CM) :
    tri y = lhs1 a b → False := by
  intro h
  have hleft : y = a := (CM.p.inj h).1
  have hright : p y y = p (q b) (q a) := (CM.p.inj h).2
  have htail : y = q a := (CM.p.inj hright).2
  have hself : y = q y := htail.trans (congrArg q hleft.symm)
  have hs := congrArg sz hself
  simp [q, tri, sz] at hs
  omega

theorem op_tri_raw (y : CM) : op y (p y y) = tri y := by
  change root (tri y) = tri y
  apply root_eq_self
  · exact no_tri_lhs0 y _ _
  · exact no_tri_lhs1 y _ _

theorem no_q_lhs0 (y a x : CM) :
    q y = lhs0 a x → False := by
  intro h
  have hleft : tri y = p a (q x) := (CM.p.inj h).1
  have hright : y = a := (CM.p.inj h).2
  have hleft' : tri y = p y (q x) :=
    hleft.trans (congrArg (fun t => p t (q x)) hright.symm)
  have htail : p y y = q x := (CM.p.inj hleft').2
  have hx1 : y = tri x := (CM.p.inj htail).1
  have hx2 : y = x := (CM.p.inj htail).2
  have hself : x = tri x := hx2.symm.trans hx1
  have hs := congrArg sz hself
  simp [tri, sz] at hs
  omega

theorem no_q_lhs1 (y a b : CM) :
    q y = lhs1 a b → False := by
  intro h
  have hleft : tri y = a := (CM.p.inj h).1
  have hright : y = p (q b) (q a) := (CM.p.inj h).2
  have hself : y = p (q b) (q (tri y)) :=
    hright.trans (congrArg (fun t => p (q b) (q t)) hleft.symm)
  have hs := congrArg sz hself
  simp [q, tri, sz] at hs
  omega

theorem op_q_raw (y : CM) : op (tri y) y = q y := by
  change root (q y) = q y
  apply root_eq_self
  · exact no_q_lhs0 y _ _
  · exact no_q_lhs1 y _ _

theorem mid_ne_lhs1 (x y a b : CM) :
    p y (q x) = lhs1 a b → False := by
  intro h
  have hright : q x = p (q b) (q a) := (CM.p.inj h).2
  have hfirst : tri x = q b := (CM.p.inj hright).1
  have hx : x = tri b := (CM.p.inj hfirst).1
  have hb : p x x = b := (CM.p.inj hfirst).2
  have hself : x = tri (p x x) :=
    hx.trans (congrArg tri hb.symm)
  have hs := congrArg sz hself
  simp [tri, sz] at hs
  omega

theorem source_holds (x y : CM) :
    x = op (op y (op (op x (op x x)) x)) y := by
  rw [op_yy_raw, op_tri_raw, op_q_raw]
  let u := get0x (p y (q x))
  by_cases hm : p y (q x) = lhs0 (q x) u
  · have hy : y = p (q x) (q u) := (CM.p.inj hm).1
    have hmid : op y (q x) = u := by
      unfold op
      change root (p y (q x)) = u
      unfold root
      change
        (if p y (q x) = lhs0 (q x) u then u
          else
            if p y (q x) =
                lhs1 (get1a (p y (q x))) (get1b (p y (q x)))
              then get1b (p y (q x)) else p y (q x)) = u
      rw [if_pos hm]
    rw [hmid, hy]
    exact (op_rule1 u x).symm
  · have hmid : op y (q x) = p y (q x) := by
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
          (CM.p CM.e
            (CM.p
              (CM.p
                (CM.p CM.e CM.e)
                (CM.p CM.e CM.e))
              (CM.p CM.e CM.e)))
          CM.e at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32086_to_31937 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_32086_to_31937
