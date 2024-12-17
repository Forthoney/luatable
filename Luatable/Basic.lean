axiom Float.isInt : Float → Bool

inductive TObject where
  | nil
  | boolean (b: Bool)
  | lightUserData (pointer: USize)
  | number (n: Float) -- Before Lua 5.2, Lua exclusively used doubles for numbers
  | string (hashVal size: Nat)
  | collectible (gcObj : USize)

structure Node where
  key: TObject
  val: TObject

structure Table where
  limit : Nat
  array : List TObject
  node : List Node
  metatable: Table

def maxBits := 24
def tooBig (x : UInt32) : Bool := (x - 1) >>> maxBits.toUInt32 ≠ 0

def UInt64.nthByte (x i : UInt64) : UInt64 :=
  x <<< i &&& 0xff

noncomputable def Float.accumulate (x: Float) : List UInt8 :=
  let castedX := x.toBits
  List.range' 0 8 8 |>.map Nat.toUInt64 |>.map castedX.nthByte |>.map UInt64.toUInt8

def lmod (s size : Nat) := s &&& (size - 1)

lemma Nat.or_one (x : Nat) : x ||| 1 ≤ x + 1 := by sorry
lemma Nat.or_one_pos (x : Nat) : x ||| 1 > 0 := by sorry

namespace Table

def lsizenode (t : Table) : Nat := t.node.length.log2
def sizenode (t : Table) : Nat := 2 ^ t.lsizenode

def hashpow2' (t: Table) (nodeExists : t.node.length > 0) (n: Nat) : Fin t.node.length :=
  ⟨lmod n t.sizenode,
   by
    rw[lmod, sizenode, lsizenode]
    simp
    calc
      n % 2 ^ t.node.length.log2 < 2 ^ t.node.length.log2 := by
        apply Nat.mod_lt
        exact Nat.two_pow_pos t.node.length.log2
      _ ≤ t.node.length := by
        apply Nat.log2_self_le
        exact Nat.not_eq_zero_of_lt nodeExists⟩

def hashpow2 (t: Table)  (nodeExists : t.node.length > 0) (n: Nat) : Node :=
  t.node[t.hashpow2' nodeExists n]

def hashmod' (t: Table) (nodeExists : t.node.length > 0) (n: Nat) : Fin t.node.length :=
  ⟨n % ((t.sizenode - 1) ||| 1),
   by
    have h : t.sizenode - 1 ||| 1 < t.node.length := by
      sorry
    calc
      n % (t.sizenode - 1 ||| 1) < t.sizenode - 1 ||| 1 := by
        apply n.mod_lt
        exact Nat.or_one_pos (t.sizenode - 1)
      _ < t.node.length := h⟩

def hashmod (t: Table) (nodeExists : t.node.length > 0) (n: Nat) : Node :=
  t.node[t.hashmod' nodeExists n]

def hashpointer (t: Table) (nodeExists : t.node.length > 0) (p: USize) : Node :=
  t.hashmod nodeExists p.toNat

def hashstring' (t: Table) (nodeExists: t.node.length > 0) : Nat → Fin t.node.length :=
  t.hashpow2' nodeExists

def hashstring (t: Table) (nodeExists: t.node.length > 0) : Nat → Node :=
  t.hashpow2 nodeExists

noncomputable def hashnum' (t: Table) (nodeExists: t.node.length > 0) (n: Float) : Fin t.node.length :=
  t.hashmod' nodeExists (n + 1).accumulate.sum.toNat

noncomputable def hashnum (t: Table) (nodeExists: t.node.length > 0) (n: Float) : Node :=
  t.hashmod nodeExists (n + 1).accumulate.sum.toNat


def hash (t: Table) (nodeExists : t.node.length > 0) : TObject → Node
  | TObject.string hv size => t.hashstring nodeExists hv
  | TObject.number n => t.hashnum nodeExists n
  | TObject.nil => sorry
  | TObject.boolean b => t.hashpow2 nodeExists b.toNat
  | TObject.lightUserData p => t.hashpointer nodeExists p
  | TObject.collectible gc => t.hashpointer nodeExists gc

noncomputable def mainPosition (t : Table) : TObject → Node := t.hash sorry

def arrayIndex (n: Float) : Option UInt32 :=
  let rounded := n.toUInt32
  if rounded >= 1 ∧ ¬tooBig rounded then
    some rounded
  else
    none

def index (t: Table) : TObject → Option UInt32
  | TObject.nil => none
  | TObject.number n =>
    arrayIndex n |>.bind λ i ↦
    if i ≥ 0 ∧ i.toNat ≤ t.array.length then
      some (i - 1)
    else
      none
  | key => none

def get (t: Table) : TObject → TObject
  | TObject.string hv size =>
    let startIdx := t.hashstring' sorry hv
    let startNode := t.hashstring sorry hv
    let found := (t.node.drop startIdx).find? λ n ↦
      match n.key with
      | TObject.string hashVal _ => hashVal = hv
      | _ => false
    match found with
    | some n => n.val
    | none => TObject.nil
  | TObject.number n =>
    if n.isInt then
      if 1 ≤ n ∧ n.toNat ≤ t.array.length then
        t.array[n - 1]
      else
        let startIdx := t.hashnum' sorry n
        let startNode := t.hashnum sorry n
        let found := (t.node.drop startIdx).find? λ n ↦
          match n.key with
          | TObject.number nv => nv = hv
          | _ => false
        match found with
        | some n => n.val
        | none => TObject.nil
    else
      sorry
  | default => sorry


end Table
