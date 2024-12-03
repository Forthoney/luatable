import Mathlib.Data.Vector.Basic

abbrev TBoolean := Bool
abbrev TNumber := UInt64 -- Using this for now becuse Float is very cumbersome to use

structure TString where
  hash : Nat
  size : Nat

inductive TObject where
  | string (str: TString)
  | number (n: TNumber) -- Up to Lua 5.2, Lua exclusively used doubles for numbers
  | nil
  | bool (b: TBoolean)
  | light_user_value (pointer: USize)

structure Node where
  key: TObject
  val: TObject

structure Table where
  limit : Nat
  array : List TValue
  node : List Node
  metatable: Table

def maxBits := 24
def tooBig (x : UInt32) : Bool := (x - 1) >>> maxBits.toUInt32 ≠ 0

def TNumber.nthByte (x i : TNumber) : TNumber :=
  x <<< i &&& 0xff

def TNumber.memcpy (x: TNumber) : List UInt8 :=
  List.range' 0 8 8 |>.map Nat.toUInt64 |>.map x.nthByte |>.map UInt64.toUInt8

def lmod (s size : Nat) := s &&& (size - 1)

lemma Nat.or_one (x : Nat) : x ||| 1 ≤ x + 1 := by sorry
lemma Nat.or_one_pos (x : Nat) : x ||| 1 > 0 := by sorry

namespace Table

def lsizenode (t : Table) : Nat := t.node.length.log2
def sizenode (t : Table) : Nat := 2 ^ t.lsizenode


def hashpow2 (t: Table) (n: Nat) (node_exists : t.node.length > 0) : Node :=
  t.node[lmod n t.sizenode]'
  (by
    rw[lmod, sizenode, lsizenode]
    simp
    calc
      n % 2 ^ t.node.length.log2 < 2 ^ t.node.length.log2 := by
        apply Nat.mod_lt
        exact Nat.two_pow_pos t.node.length.log2
      _ ≤ t.node.length := by
        apply Nat.log2_self_le
        exact Nat.not_eq_zero_of_lt node_exists)

def hashmod (t: Table) (n: Nat) (node_exists : t.node.length > 0): Node :=
  t.node[n % ((t.sizenode - 1) ||| 1)]'
  (by
    have h : t.sizenode - 1 ||| 1 < t.node.length := by
      sorry
    calc
      n % (t.sizenode - 1 ||| 1) < t.sizenode - 1 ||| 1 := by
        apply n.mod_lt
        exact Nat.or_one_pos (t.sizenode - 1)
      _ < t.node.length := h)

class Hashable (α : Type) where
  hashnode (val : α) (t : Table) (node_exists : t.node.length > 0) : Node

instance : Hashable TString where
  hashnode := λ str t ex ↦ t.hashpow2 str.hash ex

instance : Hashable TNumber where
  hashnode := λ n t ex ↦  t.hashmod (n + 1).memcpy.sum.toNat ex

instance : Hashable TBoolean where
  hashnode := λ b t ex ↦ t.hashpow2 b.toNat ex

instance : Hashable USize where
  hashnode := λ p t ex ↦ t.hashmod p.toUInt32.toNat ex

def mainPosition (t : Table) (key : TObject) : Node :=
  match key with
  | TObject.string str => Hashable.hashnode str t sorry
  | TObject.number n => Hashable.hashnode n t sorry
  | TObject.bool b => Hashable.hashnode b t sorry
  | TObject.light_user_value p => Hashable.hashnode p t sorry
  | _ => sorry

def arrayIndex (key: TObject) : Option UInt32 :=
  match key with
  | TObject.number n =>
    let rounded := n.toUInt32
    if rounded >= 1 ∧ ¬tooBig rounded then
      some rounded
    else
      none
  | _ => none

end Table
