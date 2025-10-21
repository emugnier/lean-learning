import LeanLearning

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

class Plus (α : Type) where
  plus : α → α → α

instance : One Pos where
  one := Pos.one

def seven : Pos :=
  (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one))))))

def Pos.plus : Pos → Pos → Pos
  | Pos.one, n => Pos.succ n
  | Pos.succ n, m => Pos.succ (n.plus m)

def Pos.mul : Pos -> Pos → Pos
  | Pos.one, n => n
  | Pos.succ m, n => n.plus (m.mul n)

instance: Mul Pos where
  mul := Pos.mul

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos :=
  Plus.plus seven seven

#eval fourteen  -- should evaluate to 14 successors of one

def posToString (atTop: Bool) (p: Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString p := posToString true p

#eval toString fourteen  -- should print the structure of fourteen

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => 1 + n.toNat

instance: ToString Pos where
  toString p := toString p.toNat

#eval toString fourteen  -- should print "14"
#eval s!"fourteen Pos as Nat: {fourteen}"

#eval [seven * Pos.one, fourteen * seven, fourteen * fourteen]

instance : OfNat Pos (n+1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | n+1 => Pos.succ (natPlusOne n)
    natPlusOne n

def hashPos : Pos → UInt64
| Pos.one => 0
| Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance [Hashable α] : Hashable (NonEmptyList α) where
 hash xs := mixHash (hash xs.head) (hash xs.tail)

inductive BinTree (α : Type) where
| leaf : BinTree α
| branch: BinTree α → α -> BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α -> BinTree α → Bool
| BinTree.leaf, BinTree.leaf => true
| BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
x == x2 && eqBinTree l l2 && eqBinTree r r2
| _, _ => false

instance [BEq α] : BEq (BinTree α) where
 beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
| BinTree.leaf => 0
| BinTree.branch l x r =>
  mixHash (hashBinTree l)
        (mixHash (hash x)
          (hashBinTree r))

instance [Hashable α] : Hashable (BinTree α) where
 hash := hashBinTree

instance : Append (NonEmptyList α) where
 append xs ys :=
  { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail}
