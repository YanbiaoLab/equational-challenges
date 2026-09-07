-- Equation2903 → Equation31222
-- Recorded verdict: false
-- Premise: x = ((y ◇ (x ◇ x)) ◇ y) ◇ y
-- Conclusion: x = (y ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ y
-- Original submission SHA-256: 5b2a3a6d825f48f32c794af57af123ea72150d2258dfce6537d476de2f024927
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((y ◇ (x ◇ x)) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ y
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

def d (a b : CM) : CM :=
  p (p (sq b) (sq a)) (sq b)

def lhs0 (a x : CM) : CM :=
  p (p (p a (sq x)) a) a

def lhs1 (a b : CM) : CM :=
  p (p a (d a b)) (d a b)

def get0a : CM → CM
  | p _ a => a
  | _ => e

def get0x : CM → CM
  | p (p (p _ (p x _)) _) _ => x
  | _ => e

def get1a : CM → CM
  | p (p a _) _ => a
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

theorem lhs1_not_lhs0 (a b c x : CM) :
    lhs1 a b = lhs0 c x → False := by
  intro h
  have hr : d a b = c := (CM.p.inj h).2
  have hl : a = p c (sq x) := (CM.p.inj (CM.p.inj h).1).1
  have hself : a = p (d a b) (sq x) := by
    exact hl.trans (congrArg (fun q => p q (sq x)) hr.symm)
  have hs := congrArg sz hself
  simp [d, sq, sz] at hs
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
    (if lhs1 a b = lhs0 (d a b) (get0x (lhs1 a b))
      then get0x (lhs1 a b)
      else if lhs1 a b = lhs1 a b then b else lhs1 a b) = b
  rw [if_neg (lhs1_not_lhs0 a b _ _), if_pos rfl]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0a t) (get0x t) → False)
    (h1 : t = lhs1 (get1a t) (get1b t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1]

theorem op_rule0 (a x : CM) :
    op (p (p a (sq x)) a) a = x := by
  exact root_lhs0 a x

theorem op_rule1 (a b : CM) :
    op (p a (d a b)) (d a b) = b := by
  exact root_lhs1 a b

theorem no_xx_lhs0 (q a x : CM) :
    p q q = lhs0 a x → False := by
  intro h
  have hl : q = p (p a (sq x)) a := (CM.p.inj h).1
  have hr : q = a := (CM.p.inj h).2
  have hself : a = p (p a (sq x)) a := hr.symm.trans hl
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem no_xx_lhs1 (q a b : CM) :
    p q q = lhs1 a b → False := by
  intro h
  have hl : q = p a (d a b) := (CM.p.inj h).1
  have hr : q = d a b := (CM.p.inj h).2
  have hself : d a b = p a (d a b) := hr.symm.trans hl
  have hs := congrArg sz hself
  simp [d, sq, sz] at hs
  omega

theorem op_xx_raw (q : CM) : op q q = p q q := by
  unfold op
  apply root_eq_self
  · exact no_xx_lhs0 q _ _
  · exact no_xx_lhs1 q _ _

theorem mid_not_lhs1 (x y a b : CM) :
    p y (sq x) = lhs1 a b → False := by
  intro h
  have hr : sq x = d a b := (CM.p.inj h).2
  have hleft : x = p (sq b) (sq a) := (CM.p.inj hr).1
  have hright : x = sq b := (CM.p.inj hr).2
  have hself : sq b = p (sq b) (sq a) :=
    hright.symm.trans hleft
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem prefix0_not_lhs0 (x y a b : CM) :
    p (p y (sq x)) y = lhs0 a b → False := by
  intro h
  have hr : y = a := (CM.p.inj h).2
  have hl : y = p a (sq b) := (CM.p.inj (CM.p.inj h).1).1
  have hself : a = p a (sq b) := hr.symm.trans hl
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem prefix0_not_lhs1 (x y a b : CM) :
    p (p y (sq x)) y = lhs1 a b → False := by
  intro h
  have hr : y = d a b := (CM.p.inj h).2
  have hl : y = a := (CM.p.inj (CM.p.inj h).1).1
  have hself : a = d a b := hl.symm.trans hr
  have hs := congrArg sz hself
  simp [d, sq, sz] at hs
  omega

theorem op_prefix0_raw (x y : CM) :
    op (p y (sq x)) y = p (p y (sq x)) y := by
  unfold op
  apply root_eq_self
  · exact prefix0_not_lhs0 x y _ _
  · exact prefix0_not_lhs1 x y _ _

theorem prefix1_not_lhs0 (a b c x : CM) :
    p a (d a b) = lhs0 c x → False := by
  intro h
  have hr : d a b = c := (CM.p.inj h).2
  have hl : a = p (p c (sq x)) c := (CM.p.inj h).1
  have hself : a = p (p (d a b) (sq x)) (d a b) := by
    exact hl.trans
      (congrArg (fun q => p (p q (sq x)) q) hr.symm)
  have hs := congrArg sz hself
  simp [d, sq, sz] at hs
  omega

theorem prefix1_not_lhs1 (a b c x : CM) :
    p a (d a b) = lhs1 c x → False := by
  intro h
  have hr : d a b = d c x := (CM.p.inj h).2
  have hl : a = p c (d c x) := (CM.p.inj h).1
  have hs1 := congrArg sz hr
  have hs2 := congrArg sz hl
  simp [d, sq, sz] at hs1 hs2
  omega

theorem op_prefix1_raw (a b : CM) :
    op a (d a b) = p a (d a b) := by
  unfold op
  apply root_eq_self
  · exact prefix1_not_lhs0 a b _ _
  · exact prefix1_not_lhs1 a b _ _

theorem source_holds (x y : CM) :
    x = op (op (op y (op x x)) y) y := by
  rw [op_xx_raw]
  change x = op (op (op y (sq x)) y) y
  let b := get0x (p y (sq x))
  by_cases h : p y (sq x) = lhs0 (sq x) b
  · have hy : y = d b x := by
      simpa [lhs0, d] using (CM.p.inj h).1
    have hmid : op y (sq x) = b := by
      unfold op
      rw [h]
      exact root_lhs0 (sq x) b
    rw [hmid, hy, op_prefix1_raw]
    exact (op_rule1 b x).symm
  · have hmid : op y (sq x) = p y (sq x) := by
      unfold op
      apply root_eq_self
      · exact h
      · exact mid_not_lhs1 x y _ _
    rw [hmid, op_prefix0_raw]
    exact (op_rule0 y x).symm

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e CM.e
    change
      CM.e =
        CM.p
          (CM.p CM.e
            (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e)))
          CM.e at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2903_to_31222 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2903_to_31222
