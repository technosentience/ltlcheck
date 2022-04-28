import Ltlcheck.Automata

/-- Type of LTL formulas indexed by a type of elementary propositions. -/
inductive LTLFormula (p : Type u) where
  | tru : LTLFormula p
  | prim : p → LTLFormula p
  | neg : LTLFormula p → LTLFormula p
  | andf : LTLFormula p → LTLFormula p → LTLFormula p
  | next : LTLFormula p → LTLFormula p
  | untl : LTLFormula p → LTLFormula p → LTLFormula p
deriving Repr

open LTLFormula

def ltlBEQ [BEq p] : LTLFormula p → LTLFormula p → Bool
  | tru, tru => true
  | prim a, prim b => a == b
  | neg a, neg b => ltlBEQ a b
  | andf a a', andf b b' => ltlBEQ a b && ltlBEQ a' b'
  | next a, next b => ltlBEQ a b
  | untl a a', untl b b' => ltlBEQ a b && ltlBEQ a' b'
  | _, _ => false

def ltlHash [Hashable p] : LTLFormula p → UInt64
  | tru => 3
  | prim p' => mixHash 7 (hash p')
  | neg a => mixHash 11 (ltlHash a)
  | andf a b => mixHash 13 (mixHash (ltlHash a) (ltlHash b))
  | next a => mixHash 19 (ltlHash a)
  | untl a b => mixHash 23 (mixHash (ltlHash a) (ltlHash b))

instance [BEq p] : BEq (LTLFormula p) where
  beq := ltlBEQ

instance [Hashable p] : Hashable (LTLFormula p) where
  hash := ltlHash

def restrictLTL [BEq p] [Hashable p] (hs : Std.HashSet p) : LTLFormula p → LTLFormula (Subset hs)
  | tru => tru
  | prim p' => match decEq (hs.contains p') true with
    | isTrue h => prim ⟨p', h⟩
    | isFalse _ => neg tru
  | neg x => neg (restrictLTL hs x)
  | andf x y => andf (restrictLTL hs x) (restrictLTL hs y)
  | next x => next (restrictLTL hs x)
  | untl x y => untl (restrictLTL hs x) (restrictLTL hs y)

def atoms [BEq p] [Hashable p] : LTLFormula p → Std.HashSet p
  | tru => {}
  | prim p' => Std.HashSet.empty.insert p'
  | neg x => atoms x
  | andf x y => hashSetUnion (atoms x) (atoms y)
  | next x => atoms x
  | untl x y => hashSetUnion (atoms x) (atoms y)

def neg' : LTLFormula p → LTLFormula p
  | neg x => x
  | x => neg x

def subformulas [BEq p] [Hashable p] : LTLFormula p → Std.HashSet (LTLFormula p)
  | neg x => (subformulas x).insert (neg x)
  | andf x y => (hashSetUnion (subformulas x) (subformulas y)).insert (andf x y)
  | next x => (subformulas x).insert (next x)
  | untl x y => (hashSetUnion (subformulas x) (subformulas y)).insert (untl x y)
  | x => Std.HashSet.empty.insert x 

def closure [BEq p] [Hashable p] (f : LTLFormula p) : Std.HashSet (LTLFormula p) :=
  let sf := (subformulas f).insert tru
  hashSetUnion sf (hashSetMap neg' sf)

def elementary [BEq p] [Hashable p] {f : LTLFormula p} (s : Std.HashSet (Subset (closure f))) : Bool
  :=
    let cl := (closure f).toArray
    contains' s tru
    && cl.all (fun x => (contains' s x) != (contains' s (neg' x)))
    && cl.all (fun xy => if let andf x y := xy then
      (contains' s x && contains' s y) == (contains' s xy) else true)
    && cl.all (fun xy => if let untl x y := xy then
      (not (contains' s y) || contains' s xy)
      && ((not (contains' s xy) || contains' s y) || contains' s x) else true)

def ElemState [BEq p] [Hashable p] (f : LTLFormula p) := { hs : Std.HashSet (Subset (closure f)) // elementary hs }

@[defaultInstance]
instance [BEq p] [Hashable p] {f : LTLFormula p} : BEq (ElemState f) where
  beq x y := x.val == y.val

@[defaultInstance]
instance [BEq p] [Hashable p] {f : LTLFormula p} : Hashable (ElemState f) where
  hash x := hash x.val

@[defaultInstance]
instance [BEq p] [Hashable p] [Repr p] {f : LTLFormula p} : Repr (ElemState f) where
  reprPrec x := reprPrec x.val

def elemStates [BEq p] [Hashable p] (f : LTLFormula p) : Array (ElemState f) :=
  (subsets (closure f)).filterMap (fun s => match decEq (elementary s) true with
    | isTrue h => some ⟨s, h⟩
    | isFalse _ => none)

def elemAtoms [BEq p] [Hashable p] {f : LTLFormula p} (s : ElemState f) : Std.HashSet (Subset (atoms f))
  := s.val.fold (fun hs f' => if let prim p' := f'.val then
      match decEq ((atoms f).contains p') true with
      | isTrue h => hs.insert ⟨p', h⟩
      | isFalse _ => hs
      else hs) {}

def isStart [BEq p] [Hashable p] {f : LTLFormula p} (e : ElemState f) : Bool :=
  contains' e.val f

def isNext [BEq p] [Hashable p] {f : LTLFormula p} (e e' : ElemState f) : Bool :=
  let cl := (closure f).toArray
  cl.all (fun nx => if let next x := nx then
    (contains' e.val nx) == (contains' e'.val x) else true)
  && cl.all (fun xy => if let untl x y := xy then
    (contains' e.val xy) == (contains' e'.val y || (contains' e'.val x && contains' e'.val xy)) else true)

def buchiLTLFinal [BEq p] [Hashable p] (f : LTLFormula p) : Array (Option (ElemState f) → Bool) :=
  (closure f).toArray.filterMap (fun xy => if let untl x y := xy then
    some (fun st => if let some st := st then contains' st.val y || not (contains' st.val xy) else false) else none)

def buchiOfLTL [BEq p] [Hashable p] (f : LTLFormula p)
  : GeneralizedBuchiAutomata (Option (ElemState f)) (Std.HashSet (Subset (atoms f))) where
  init := #[none] --
  next := let es := elemStates f
    fun
      | some s => (es.filter (isNext s)).map (fun s' => (elemAtoms s', s'))
      | none => (es.filter isStart).map (fun s' => (elemAtoms s', s'))
  final := (buchiLTLFinal f).back?.getD (fun _ => false)
  finals := (buchiLTLFinal f).pop
