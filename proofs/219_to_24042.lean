-- Equation219 → Equation24042
-- Recorded verdict: false
-- Premise: x = (y ◇ (x ◇ x)) ◇ y
-- Conclusion: x = ((x ◇ y) ◇ x) ◇ ((x ◇ x) ◇ y)
-- Original submission SHA-256: e96c19ce0649442111b8a3291ce61bb57944488fe065ec1197a6c1265f474aa4
-- Aurora-accepted correction SHA-256: 1510bfc3d3954166e305ac60df2dda9794601a0c36bd11beb58db777e9bd8dcc
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (x ◇ x)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ y) ◇ x) ◇ ((x ◇ x) ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     

namespace submission

set_option maxRecDepth 2000

namespace Equation219TreeModel

inductive V where
  | base
  | s (x : V)
  | t (key value : V)
  deriving DecidableEq

def specialSS : V → V → Option V
  | .s (.s x), .s y => if x = y then some x else none
  | _, _ => none

def specialXS : V → V → Option V
  | x, .s (.s y) => if x = y then some x else none
  | _, _ => none

def decodeLeft : V → V → Option V
  | .t key value, y => if key = y then some value else none
  | _, _ => none

def decodeRight : V → V → Option V
  | x, .t (.s preimage) value => if value = x then some preimage else none
  | _, _ => none

def encode : V → V → Option V
  | x, .s preimage => some (.t x preimage)
  | _, _ => none

def op (x y : V) : V :=
  if x = y then .s x else
    (specialSS x y).getD
      ((specialXS x y).getD
        ((decodeLeft x y).getD
          ((decodeRight x y).getD
            ((encode x y).getD .base))))

def size : V → Nat
  | .base => 1
  | .s x => size x + 1
  | .t x y => size x + size y + 1

theorem size_pos (x : V) : 0 < size x := by
  induction x <;> simp [size, *]

@[simp] theorem s_ne_self (x : V) : V.s x ≠ x := by
  intro h
  have := congrArg size h
  simp [size] at this

@[simp] theorem self_ne_s (x : V) : x ≠ V.s x := Ne.symm (s_ne_self x)

@[simp] theorem self_ne_ss (x : V) : x ≠ V.s (V.s x) := by
  intro h
  have e := congrArg size h
  simp [size] at e
  omega

@[simp] theorem self_ne_sss (x : V) : x ≠ V.s (V.s (V.s x)) := by
  intro h
  have e := congrArg size h
  simp [size] at e
  omega

@[simp] theorem t_ne_left (x y : V) : V.t x y ≠ x := by
  intro h
  have eq := congrArg size h
  have pos := size_pos y
  simp [size] at eq
  omega

@[simp] theorem left_ne_t (x y : V) : x ≠ V.t x y := Ne.symm (t_ne_left x y)

@[simp] theorem t_ne_right (x y : V) : V.t x y ≠ y := by
  intro h
  have eq := congrArg size h
  have pos := size_pos x
  simp [size] at eq
  omega

@[simp] theorem right_ne_t (x y : V) : y ≠ V.t x y := Ne.symm (t_ne_right x y)

@[simp] theorem op_self (x : V) : op x x = .s x := by
  simp [op]

@[simp] theorem op_ss_s (x : V) : op (.s (.s x)) (.s x) = x := by
  simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode]

@[simp] theorem op_x_ss (x : V) : op x (.s (.s x)) = x := by
  cases x with
  | base => rfl
  | s a =>
      cases a with
      | base => rfl
      | s z =>
          have h : z ≠ V.s (V.s (V.s z)) := by
            intro eq
            have e := congrArg size eq
            simp [size] at e
            omega
          simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode, h]
      | t k v =>
          simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode]
  | t k v =>
      simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode]

@[simp] theorem op_t_left (key value : V) : op (.t key value) key = value := by
  cases key with
  | base => rfl
  | s a =>
      cases a with
      | base => rfl
      | s z =>
          have h : V.t (V.s (V.s z)) value ≠ z := by
            intro eq
            have e := congrArg size eq
            have p := size_pos value
            simp [size] at e
            omega
          simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode, h]
      | t k v =>
          simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode]
  | t k v =>
      simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode]

@[simp] theorem op_t_right (x value : V) : op value (.t (.s x) value) = x := by
  cases value with
  | base => rfl
  | s v =>
      simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode]
  | t key payload =>
      have h : key ≠ V.t (V.s x) (V.t key payload) := by
        intro eq
        have e := congrArg size eq
        have p := size_pos x
        have q := size_pos payload
        simp [size] at e
        omega
      simp [op, specialSS, specialXS, decodeLeft, decodeRight, encode, h]

theorem specialSS_s_none {x y : V} (h : y ≠ V.s (V.s x)) :
    specialSS y (.s x) = none := by
  cases y with
  | base => rfl
  | s a =>
      cases a with
      | base => rfl
      | s z =>
          have hz : z ≠ x := by
            intro eq
            subst z
            exact h rfl
          simp [specialSS, hz]
      | t key value => rfl
  | t key value => rfl

theorem specialXS_s_none {x y : V} (h : x ≠ V.s y) :
    specialXS y (.s x) = none := by
  cases x with
  | base => rfl
  | s z =>
      have hz : y ≠ z := by
        intro eq
        subst y
        exact h rfl
      simp [specialXS, hz]
  | t key value => rfl

theorem source (x y : V) : op (op y (op x x)) y = x := by
  rw [op_self]
  by_cases h1 : y = V.s x
  · subst y
    simp
  by_cases h2 : y = V.s (V.s x)
  · subst y
    simp
  by_cases h3 : x = V.s y
  · subst x
    simp
  cases y with
  | base =>
      have inner : op .base (.s x) = .t .base x := by
        rw [op, if_neg h1, specialSS_s_none h2, specialXS_s_none h3]
        rfl
      simp [inner]
  | s a =>
      have inner : op (.s a) (.s x) = .t (.s a) x := by
        rw [op, if_neg h1, specialSS_s_none h2, specialXS_s_none h3]
        rfl
      simp [inner]
  | t key value =>
      by_cases hk : key = V.s x
      · subst key
        simp
      · have inner : op (.t key value) (.s x) = .t (.t key value) x := by
          rw [op, if_neg h1, specialSS_s_none h2, specialXS_s_none h3]
          simp [decodeLeft, decodeRight, encode, hk]
        simp [inner]

theorem target_not :
    ¬ ∀ x y : V, x = op (op (op x y) x) (op (op x x) y) := by
  intro h
  have bad := h .base .base
  exact V.noConfusion bad

end Equation219TreeModel

def certificate : Goal := by
  refine ⟨Equation219TreeModel.V, ⟨Equation219TreeModel.op⟩, ?_, ?_⟩
  · intro x y
    exact (Equation219TreeModel.source x y).symm
  · exact Equation219TreeModel.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_219_to_24042 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_219_to_24042
