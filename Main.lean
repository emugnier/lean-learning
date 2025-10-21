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

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
