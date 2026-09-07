-- Equation4916 → Equation17024
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (x ◇ (y ◇ (z ◇ z))))
-- Conclusion: x = (x ◇ x) ◇ (y ◇ (z ◇ (w ◇ u)))
-- Original submission SHA-256: 8e9af349ea200623b2684505bfff2f2b23777ddc4c9b6eac71587d2c1dfb4ebe
-- Aurora-accepted correction SHA-256: fef7f92537cf334251c212bf447dfa8ded11a448b58c097efd57d70db66acf07
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Mathlib

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (x ◇ (y ◇ (z ◇ z))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ x) ◇ (y ◇ (z ◇ (w ◇ u)))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
              

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

def lhs0 (y x z : CM) : CM :=
  p y (p x (p x (p y (sq z))))

def lhs1 (z : CM) : CM :=
  p (sq z) (sq z)

def lhs2 (x z : CM) : CM :=
  p (p x (sq z)) (p x (p x (sq z)))

def lhs3 (x z : CM) : CM :=
  p (sq z) (p x (p x (sq z)))

def get0y : CM → CM
  | p y _ => y
  | _ => e

def get0x : CM → CM
  | p _ (p x _) => x
  | _ => e

def get0z : CM → CM
  | p _ (p _ (p _ (p _ (p z _)))) => z
  | _ => e

def get1z : CM → CM
  | p (p z _) _ => z
  | _ => e

def get2x : CM → CM
  | p (p x _) _ => x
  | _ => e

def get2z : CM → CM
  | p (p _ (p z _)) _ => z
  | _ => e

def get3x : CM → CM
  | p _ (p x _) => x
  | _ => e

def get3z : CM → CM
  | p (p z _) _ => z
  | _ => e

def getSq : CM → CM
  | p z _ => z
  | _ => e

def root (t : CM) : CM :=
  if t = lhs0 (get0y t) (get0x t) (get0z t) then
    get0x t
  else if t = lhs1 (get1z t) then
    sq (get1z t)
  else if t = lhs2 (get2x t) (get2z t) then
    get2x t
  else if t = lhs3 (get3x t) (get3z t) then
    get3x t
  else
    t

def op (a b : CM) : CM := root (p a b)

theorem lhs1_not_lhs0 (z y x w : CM) :
    lhs1 z = lhs0 y x w → False := by
  intro h
  have hl : sq z = y := (CM.p.inj h).1
  have hr : sq z = p x (p x (p y (sq w))) := (CM.p.inj h).2
  have hself : y = p x (p x (p y (sq w))) := hl.symm.trans hr
  have hs := congrArg sz hself
  simp [lhs0, lhs1, sq, sz] at hs
  omega

theorem lhs2_not_lhs0 (a z y x w : CM) :
    lhs2 a z = lhs0 y x w → False := by
  intro h
  have hl : p a (sq z) = y := (CM.p.inj h).1
  have hr :
      p a (p a (sq z)) = p x (p x (p y (sq w))) :=
    (CM.p.inj h).2
  have hxa : a = x := (CM.p.inj hr).1
  have htail :
      p a (sq z) = p x (p y (sq w)) :=
    (CM.p.inj hr).2
  have hsq : sq z = p y (sq w) := by
    exact (CM.p.inj htail).2
  have hself : sq z = p (p a (sq z)) (sq w) := by
    exact hsq.trans (congrArg (fun q => p q (sq w)) hl.symm)
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem lhs2_not_lhs1 (a z w : CM) :
    lhs2 a z = lhs1 w → False := by
  intro h
  have hl : p a (sq z) = sq w := (CM.p.inj h).1
  have hr : p a (p a (sq z)) = sq w := (CM.p.inj h).2
  have hself : p a (sq z) = p a (p a (sq z)) := hl.trans hr.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem lhs3_not_lhs0 (a z y x w : CM) :
    lhs3 a z = lhs0 y x w → False := by
  intro h
  have hl : sq z = y := (CM.p.inj h).1
  have hr :
      p a (p a (sq z)) = p x (p x (p y (sq w))) :=
    (CM.p.inj h).2
  have hax : a = x := (CM.p.inj hr).1
  have htail :
      p a (sq z) = p x (p y (sq w)) :=
    (CM.p.inj hr).2
  have hsq : sq z = p y (sq w) := (CM.p.inj htail).2
  have hself : sq z = p (sq z) (sq w) := by
    exact hsq.trans (congrArg (fun q => p q (sq w)) hl.symm)
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem lhs3_not_lhs1 (a z w : CM) :
    lhs3 a z = lhs1 w → False := by
  intro h
  have hl : sq z = sq w := (CM.p.inj h).1
  have hr : p a (p a (sq z)) = sq w := (CM.p.inj h).2
  have hself : sq z = p a (p a (sq z)) := hl.trans hr.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem lhs3_not_lhs2 (a z x w : CM) :
    lhs3 a z = lhs2 x w → False := by
  intro h
  have hl : sq z = p x (sq w) := (CM.p.inj h).1
  have hr :
      p a (p a (sq z)) = p x (p x (sq w)) :=
    (CM.p.inj h).2
  have hax : a = x := (CM.p.inj hr).1
  have htail : p a (sq z) = p x (sq w) := (CM.p.inj hr).2
  have hsq : sq z = sq w := (CM.p.inj htail).2
  have hself : sq z = p a (sq z) := by
    exact hl.trans <|
      (congrArg (fun q => p x q) hsq.symm).trans <|
        congrArg (fun q => p q (sq z)) hax.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem root_lhs0 (y x z : CM) : root (lhs0 y x z) = x := by
  change
    (if lhs0 y x z = lhs0 y x z then x
      else if lhs0 y x z = lhs1 (get1z (lhs0 y x z)) then
        sq (get1z (lhs0 y x z))
      else if lhs0 y x z =
          lhs2 (get2x (lhs0 y x z)) (get2z (lhs0 y x z)) then
        get2x (lhs0 y x z)
      else if lhs0 y x z =
          lhs3 (get3x (lhs0 y x z)) (get3z (lhs0 y x z)) then
        get3x (lhs0 y x z)
      else lhs0 y x z) = x
  rw [if_pos rfl]

theorem root_lhs1 (z : CM) : root (lhs1 z) = sq z := by
  change
    (if lhs1 z = lhs0 (sq z) (get0x (lhs1 z)) (get0z (lhs1 z))
      then get0x (lhs1 z)
      else if lhs1 z = lhs1 z then sq z
      else if lhs1 z = lhs2 (get2x (lhs1 z)) (get2z (lhs1 z))
        then get2x (lhs1 z)
      else if lhs1 z = lhs3 (get3x (lhs1 z)) (get3z (lhs1 z))
        then get3x (lhs1 z)
      else lhs1 z) = sq z
  rw [if_neg (lhs1_not_lhs0 z _ _ _), if_pos rfl]

theorem root_lhs2 (x z : CM) : root (lhs2 x z) = x := by
  change
    (if lhs2 x z =
        lhs0 (p x (sq z)) (get0x (lhs2 x z)) (get0z (lhs2 x z))
      then get0x (lhs2 x z)
      else if lhs2 x z = lhs1 (get1z (lhs2 x z))
        then sq (get1z (lhs2 x z))
      else if lhs2 x z = lhs2 x z then x
      else if lhs2 x z =
          lhs3 (get3x (lhs2 x z)) (get3z (lhs2 x z))
        then get3x (lhs2 x z)
      else lhs2 x z) = x
  rw [
    if_neg (lhs2_not_lhs0 x z _ _ _),
    if_neg (lhs2_not_lhs1 x z _),
    if_pos rfl
  ]

theorem root_lhs3 (x z : CM) : root (lhs3 x z) = x := by
  change
    (if lhs3 x z =
        lhs0 (sq z) (get0x (lhs3 x z)) (get0z (lhs3 x z))
      then get0x (lhs3 x z)
      else if lhs3 x z = lhs1 (get1z (lhs3 x z))
        then sq (get1z (lhs3 x z))
      else if lhs3 x z =
          lhs2 (get2x (lhs3 x z)) (get2z (lhs3 x z))
        then get2x (lhs3 x z)
      else if lhs3 x z = lhs3 x z then x
      else lhs3 x z) = x
  rw [
    if_neg (lhs3_not_lhs0 x z _ _ _),
    if_neg (lhs3_not_lhs1 x z _),
    if_neg (lhs3_not_lhs2 x z _ _),
    if_pos rfl
  ]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0y t) (get0x t) (get0z t) → False)
    (h1 : t = lhs1 (get1z t) → False)
    (h2 : t = lhs2 (get2x t) (get2z t) → False)
    (h3 : t = lhs3 (get3x t) (get3z t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem op_rule0 (y x z : CM) :
    op y (p x (p x (p y (sq z)))) = x := by
  exact root_lhs0 y x z

theorem op_rule1 (z : CM) :
    op (sq z) (sq z) = sq z := by
  exact root_lhs1 z

theorem op_rule2 (x z : CM) :
    op (p x (sq z)) (p x (p x (sq z))) = x := by
  exact root_lhs2 x z

theorem op_rule3 (x z : CM) :
    op (sq z) (p x (p x (sq z))) = x := by
  exact root_lhs3 x z

inductive Normal : CM → Prop where
  | e : Normal e
  | p {a b : CM} :
      Normal a →
      Normal b →
      root (p a b) = p a b →
      Normal (p a b)

theorem Normal.left {a b : CM} (h : Normal (CM.p a b)) : Normal a := by
  cases h with
  | p ha _ _ => exact ha

theorem Normal.right {a b : CM} (h : Normal (CM.p a b)) : Normal b := by
  cases h with
  | p _ hb _ => exact hb

theorem root_normal {a b : CM} (ha : Normal a) (hb : Normal b) :
    Normal (root (p a b)) := by
  unfold root
  split
  next h0 =>
    have hr := (CM.p.inj h0).2
    rw [hr] at hb
    exact hb.left
  next h0 =>
    split
    next h1 =>
      have hl := (CM.p.inj h1).1
      rw [hl] at ha
      exact ha
    next h1 =>
      split
      next h2 =>
        have hl := (CM.p.inj h2).1
        rw [hl] at ha
        exact ha.left
      next h2 =>
        split
        next h3 =>
          have hr := (CM.p.inj h3).2
          rw [hr] at hb
          exact hb.left
        next h3 =>
          exact Normal.p ha hb (root_eq_self h0 h1 h2 h3)

def NCM := {t : CM // Normal t}

def nOp (a b : NCM) : NCM :=
  ⟨op a.1 b.1, root_normal a.2 b.2⟩

instance instMagma : Magma NCM where
  op := nOp

theorem Normal.root_eq {a b : CM} (h : Normal (CM.p a b)) :
    root (CM.p a b) = CM.p a b := by
  cases h with
  | p _ _ hr => exact hr

theorem normal_not_lhs1 {q : CM} (hq : Normal q) (z : CM) :
    q = lhs1 z → False := by
  intro h
  rw [h] at hq
  have hr := hq.root_eq
  change root (lhs1 z) = lhs1 z at hr
  rw [root_lhs1] at hr
  have hs := congrArg sz hr
  simp [lhs1, sq, sz] at hs
  omega

theorem leftSq_not_lhs0 (a w y x z : CM) :
    p a (sq w) = lhs0 y x z → False := by
  intro h
  have hr :
      sq w = p x (p x (p y (sq z))) :=
    (CM.p.inj h).2
  have hwx : w = x := (CM.p.inj hr).1
  have htail : w = p x (p y (sq z)) := (CM.p.inj hr).2
  have hself : w = p w (p y (sq z)) := by
    exact htail.trans <| congrArg (fun q => p q (p y (sq z))) hwx.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem leftSq_not_lhs1 (a w z : CM)
    (hneq : a = sq w → False) :
    p a (sq w) = lhs1 z → False := by
  intro h
  have hl : a = sq z := (CM.p.inj h).1
  have hr : sq w = sq z := (CM.p.inj h).2
  exact hneq (hl.trans hr.symm)

theorem leftSq_not_lhs2 (a w x z : CM) :
    p a (sq w) = lhs2 x z → False := by
  intro h
  have hr :
      sq w = p x (p x (sq z)) :=
    (CM.p.inj h).2
  have hwx : w = x := (CM.p.inj hr).1
  have htail : w = p x (sq z) := (CM.p.inj hr).2
  have hself : w = p w (sq z) := by
    exact htail.trans <| congrArg (fun q => p q (sq z)) hwx.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem leftSq_not_lhs3 (a w x z : CM) :
    p a (sq w) = lhs3 x z → False := by
  intro h
  have hr :
      sq w = p x (p x (sq z)) :=
    (CM.p.inj h).2
  have hwx : w = x := (CM.p.inj hr).1
  have htail : w = p x (sq z) := (CM.p.inj hr).2
  have hself : w = p w (sq z) := by
    exact htail.trans <| congrArg (fun q => p q (sq z)) hwx.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem op_leftSq_raw (a w : CM) (hneq : a = sq w → False) :
    op a (sq w) = p a (sq w) := by
  unfold op
  apply root_eq_self
  · exact leftSq_not_lhs0 a w _ _ _
  · exact leftSq_not_lhs1 a w _ hneq
  · exact leftSq_not_lhs2 a w _ _
  · exact leftSq_not_lhs3 a w _ _

theorem square_not_lhs0 (q y x z : CM) :
    p q q = lhs0 y x z → False := by
  intro h
  have hl : q = y := (CM.p.inj h).1
  have hr : q = p x (p x (p y (sq z))) := (CM.p.inj h).2
  have hself : q = p x (p x (p q (sq z))) := by
    exact hr.trans <| congrArg (fun a => p x (p x (p a (sq z)))) hl.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem square_not_lhs1 (q z : CM)
    (hnot : q = sq (getSq q) → False) :
    p q q = lhs1 z → False := by
  intro h
  have hq : q = sq z := (CM.p.inj h).1
  apply hnot
  rw [hq]
  rfl

theorem square_not_lhs2 (q x z : CM) :
    p q q = lhs2 x z → False := by
  intro h
  have hl : q = p x (sq z) := (CM.p.inj h).1
  have hr : q = p x (p x (sq z)) := (CM.p.inj h).2
  have hself : p x (sq z) = p x (p x (sq z)) := hl.symm.trans hr
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem square_not_lhs3 (q x z : CM) :
    p q q = lhs3 x z → False := by
  intro h
  have hl : q = sq z := (CM.p.inj h).1
  have hr : q = p x (p x (sq z)) := (CM.p.inj h).2
  have hself : sq z = p x (p x (sq z)) := hl.symm.trans hr
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem op_square_raw (q : CM)
    (hnot : q = sq (getSq q) → False) :
    op q q = sq q := by
  unfold op
  apply root_eq_self
  · exact square_not_lhs0 q _ _ _
  · exact square_not_lhs1 q _ hnot
  · exact square_not_lhs2 q _ _
  · exact square_not_lhs3 q _ _

theorem op_square_normal (q : CM) (hq : Normal q) :
    ∃ w, op q q = sq w ∧ Normal (sq w) := by
  by_cases h : q = sq (getSq q)
  · let w := getSq q
    change q = sq w at h
    rw [h] at hq ⊢
    exact ⟨w, op_rule1 w, hq⟩
  · have hop := op_square_raw q h
    have hn := root_normal hq hq
    change Normal (op q q) at hn
    rw [hop] at hn
    exact ⟨q, hop, hn⟩

theorem middle_not_lhs1 (x y w z : CM)
    (hneq : y = sq w → False) :
    p x (p y (sq w)) = lhs1 z → False := by
  intro h
  have hr : p y (sq w) = sq z := (CM.p.inj h).2
  have hyz : y = z := (CM.p.inj hr).1
  have hwz : sq w = z := (CM.p.inj hr).2
  exact hneq (hyz.trans hwz.symm)

theorem middle_not_lhs2 (x y w a z : CM)
    (hq : Normal (sq w)) :
    p x (p y (sq w)) = lhs2 a z → False := by
  intro h
  have hr :
      p y (sq w) = p a (p a (sq z)) :=
    (CM.p.inj h).2
  have htail : sq w = p a (sq z) := (CM.p.inj hr).2
  have hwz : w = sq z := (CM.p.inj htail).2
  apply normal_not_lhs1 hq z
  simpa [lhs1, sq] using congrArg sq hwz

theorem middle_not_lhs3 (x y w a z : CM)
    (hq : Normal (sq w)) :
    p x (p y (sq w)) = lhs3 a z → False := by
  intro h
  have hr :
      p y (sq w) = p a (p a (sq z)) :=
    (CM.p.inj h).2
  have htail : sq w = p a (sq z) := (CM.p.inj hr).2
  have hwz : w = sq z := (CM.p.inj htail).2
  apply normal_not_lhs1 hq z
  simpa [lhs1, sq] using congrArg sq hwz

theorem op_middle_raw (x y w : CM)
    (hq : Normal (sq w))
    (hneq : y = sq w → False)
    (h0 :
      p x (p y (sq w)) =
        lhs0
          (get0y (p x (p y (sq w))))
          (get0x (p x (p y (sq w))))
          (get0z (p x (p y (sq w)))) →
      False) :
    op x (p y (sq w)) = p x (p y (sq w)) := by
  unfold op
  apply root_eq_self
  · exact h0
  · exact middle_not_lhs1 x y w _ hneq
  · exact middle_not_lhs2 x y w _ _ hq
  · exact middle_not_lhs3 x y w _ _ hq

theorem double_not_lhs0 (x w y a z : CM)
    (hq : Normal (sq w)) :
    p x (p x (sq w)) = lhs0 y a z → False := by
  intro h
  have hl : x = y := (CM.p.inj h).1
  have hr :
      p x (sq w) = p a (p a (p y (sq z))) :=
    (CM.p.inj h).2
  have hxa : x = a := (CM.p.inj hr).1
  have htail : sq w = p a (p y (sq z)) := (CM.p.inj hr).2
  have hw : w = a := (CM.p.inj htail).1
  have hw2 : w = p y (sq z) := (CM.p.inj htail).2
  have hself : w = p w (sq z) := by
    exact hw2.trans <| congrArg (fun q => p q (sq z)) <| hl.symm.trans hxa |>.trans hw.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem double_not_lhs1 (x w z : CM) :
    p x (p x (sq w)) = lhs1 z → False := by
  intro h
  have hl : x = sq z := (CM.p.inj h).1
  have hr : p x (sq w) = sq z := (CM.p.inj h).2
  have hself : x = p x (sq w) := hl.trans hr.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem double_not_lhs2 (x w a z : CM) :
    p x (p x (sq w)) = lhs2 a z → False := by
  intro h
  have hl : x = p a (sq z) := (CM.p.inj h).1
  have hr :
      p x (sq w) = p a (p a (sq z)) :=
    (CM.p.inj h).2
  have hxa : x = a := (CM.p.inj hr).1
  have hself : a = p a (sq z) := hxa.symm.trans hl
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem double_not_lhs3 (x w a z : CM)
    (hq : Normal (sq w)) :
    p x (p x (sq w)) = lhs3 a z → False := by
  intro h
  have hl : x = sq z := (CM.p.inj h).1
  have hr :
      p x (sq w) = p a (p a (sq z)) :=
    (CM.p.inj h).2
  have hxa : x = a := (CM.p.inj hr).1
  have htail : sq w = p a (sq z) := (CM.p.inj hr).2
  have hwa : w = a := (CM.p.inj htail).1
  apply normal_not_lhs1 hq z
  have hwz : w = sq z := hwa.trans (hxa.symm.trans hl)
  simpa [lhs1, sq] using congrArg sq hwz

theorem op_double_raw (x w : CM) (hq : Normal (sq w)) :
    op x (p x (sq w)) = p x (p x (sq w)) := by
  unfold op
  apply root_eq_self
  · exact double_not_lhs0 x w _ _ _ hq
  · exact double_not_lhs1 x w _
  · exact double_not_lhs2 x w _ _
  · exact double_not_lhs3 x w _ _ hq

theorem next_not_lhs0 (x y w a u z : CM)
    (hq : Normal (sq w)) :
    p x (p x (p y (sq w))) = lhs0 a u z → False := by
  intro h
  have hl : x = a := (CM.p.inj h).1
  have hr :
      p x (p y (sq w)) = p u (p u (p a (sq z))) :=
    (CM.p.inj h).2
  have hxu : x = u := (CM.p.inj hr).1
  have htail :
      p y (sq w) = p u (p a (sq z)) :=
    (CM.p.inj hr).2
  have hqform : sq w = p a (sq z) := (CM.p.inj htail).2
  have hwz : w = sq z := (CM.p.inj hqform).2
  apply normal_not_lhs1 hq z
  simpa [lhs1, sq] using congrArg sq hwz

theorem next_not_lhs1 (x y w z : CM) :
    p x (p x (p y (sq w))) = lhs1 z → False := by
  intro h
  have hl : x = sq z := (CM.p.inj h).1
  have hr : p x (p y (sq w)) = sq z := (CM.p.inj h).2
  have hself : x = p x (p y (sq w)) := hl.trans hr.symm
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem next_not_lhs2 (x y w a z : CM) :
    p x (p x (p y (sq w))) = lhs2 a z → False := by
  intro h
  have hl : x = p a (sq z) := (CM.p.inj h).1
  have hr :
      p x (p y (sq w)) = p a (p a (sq z)) :=
    (CM.p.inj h).2
  have hxa : x = a := (CM.p.inj hr).1
  have hself : a = p a (sq z) := hxa.symm.trans hl
  have hs := congrArg sz hself
  simp [sq, sz] at hs
  omega

theorem next_not_lhs3 (x y w a z : CM)
    (hneq : y = sq w → False) :
    p x (p x (p y (sq w))) = lhs3 a z → False := by
  intro h
  have hl : x = sq z := (CM.p.inj h).1
  have hr :
      p x (p y (sq w)) = p a (p a (sq z)) :=
    (CM.p.inj h).2
  have hxa : x = a := (CM.p.inj hr).1
  have htail : p y (sq w) = p a (sq z) := (CM.p.inj hr).2
  have hya : y = a := (CM.p.inj htail).1
  have hqz : sq w = sq z := (CM.p.inj htail).2
  exact hneq (hya.trans <| hxa.symm.trans <| hl.trans hqz.symm)

theorem op_next_raw (x y w : CM)
    (hq : Normal (sq w))
    (hneq : y = sq w → False) :
    op x (p x (p y (sq w))) = p x (p x (p y (sq w))) := by
  unfold op
  apply root_eq_self
  · exact next_not_lhs0 x y w _ _ _ hq
  · exact next_not_lhs1 x y w _
  · exact next_not_lhs2 x y w _ _
  · exact next_not_lhs3 x y w _ _ hneq

theorem source_holds (x y z : CM)
    (hx : Normal x) (hy : Normal y) (hz : Normal z) :
    x = op y (op x (op x (op y (op z z)))) := by
  rcases op_square_normal z hz with ⟨w, hsq, hq⟩
  rw [hsq]
  by_cases hyq : y = sq w
  · rw [hyq, op_rule1]
    by_cases hxq : x = sq w
    · rw [hxq, op_rule1, op_rule1, op_rule1]
    · rw [op_leftSq_raw x w hxq, op_double_raw x w hq, op_rule3]
  · rw [op_leftSq_raw y w hyq]
    let t := p x (p y (sq w))
    let a := get0y t
    let u := get0x t
    let v := get0z t
    by_cases h0 : t = lhs0 a u v
    ·
      have hc : op x (p y (sq w)) = u := by
        unfold op
        change root t = u
        rw [h0]
        exact root_lhs0 a u v
      have hr :
          p y (sq w) = p u (p u (p a (sq v))) :=
        (CM.p.inj h0).2
      have hyu : y = u := (CM.p.inj hr).1
      have htail :
          sq w = p u (p a (sq v)) :=
        (CM.p.inj hr).2
      have hwu : w = u := (CM.p.inj htail).1
      have hwrest : w = p a (sq v) := (CM.p.inj htail).2
      have hxa : x = a := (CM.p.inj h0).1
      have hyform : y = p x (sq v) := by
        exact hyu.trans <| hwu.symm.trans <|
          hwrest.trans <| congrArg (fun q => p q (sq v)) hxa.symm
      have hnv : Normal (sq v) := by
        rw [hyform] at hy
        exact hy.right
      rw [hc, ← hyu, hyform, op_double_raw x v hnv, op_rule2]
    · rw [
        op_middle_raw x y w hq hyq h0,
        op_next_raw x y w hq hyq,
        op_rule0
      ]

end CM

end submission

open submission

open submission

def submission : Goal := by
  let eN : CM.NCM := ⟨CM.e, CM.Normal.e⟩
  let qN : CM.NCM := CM.nOp eN eN
  refine ⟨CM.NCM, CM.instMagma, ?_, ?_⟩
  · intro x y z
    apply Subtype.ext
    exact CM.source_holds x.1 y.1 z.1 x.2 y.2 z.2
  · intro target
    have bad := target eN eN eN eN qN
    have badv := congrArg Subtype.val bad
    nomatch badv

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4916_to_17024 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_4916_to_17024
