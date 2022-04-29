import Ltlcheck.Automata

/-- Type of LTL formulas indexed by a type of elementary propositions. -/
inductive LTLFormula (p : Type u) where
  | tru : LTLFormula p
  | prim : p → LTLFormula p
  | neg : LTLFormula p → LTLFormula p
  | andf : LTLFormula p → LTLFormula p → LTLFormula p
  | next : LTLFormula p → LTLFormula p
  | untl : LTLFormula p → LTLFormula p → LTLFormula p
deriving BEq, Repr

open LTLFormula

-- Helper logical operators.
namespace LTLFormula
  def fal : LTLFormula p := neg tru
  def orf (x y : LTLFormula p) : LTLFormula p := neg (andf (neg x) (neg y))
  def impl (x y : LTLFormula p) : LTLFormula p := neg (andf x (neg y))
  def eqv (x y : LTLFormula p) : LTLFormula p := andf (impl x y) (impl y x)
  def rls (x y : LTLFormula p) : LTLFormula p := neg (untl (neg x) (neg y))
  def fin (x : LTLFormula p) : LTLFormula p := untl tru x
  def glob (x : LTLFormula p) : LTLFormula p := neg (fin (neg x))
end LTLFormula

-- Not ideal, but `deriving Hashable` crashes the language server for some reason.
def ltlHash [Hashable p] : LTLFormula p → UInt64
  | tru => 3
  | prim p' => mixHash 7 (hash p')
  | neg a => mixHash 11 (ltlHash a)
  | andf a b => mixHash 13 (mixHash (ltlHash a) (ltlHash b))
  | next a => mixHash 19 (ltlHash a)
  | untl a b => mixHash 23 (mixHash (ltlHash a) (ltlHash b))

instance [Hashable p] : Hashable (LTLFormula p) where
  hash := ltlHash

/-- The set of elementary propositions in a formula. -/
def atoms [BEq p] [Hashable p] : LTLFormula p → Std.HashSet p
  | tru => {}
  | prim p' => Std.HashSet.empty.insert p'
  | neg x => atoms x
  | andf x y => hashSetUnion (atoms x) (atoms y)
  | next x => atoms x
  | untl x y => hashSetUnion (atoms x) (atoms y)

/-- Negation of a formula. -/
def neg' : LTLFormula p → LTLFormula p
  | neg x => x
  | x => neg x

/-- The set of subformulas of a formula. -/
def subformulas [BEq p] [Hashable p] : LTLFormula p → Std.HashSet (LTLFormula p)
  | neg x => (subformulas x).insert (neg x)
  | andf x y => (hashSetUnion (subformulas x) (subformulas y)).insert (andf x y)
  | next x => (subformulas x).insert (next x)
  | untl x y => (hashSetUnion (subformulas x) (subformulas y)).insert (untl x y)
  | x => Std.HashSet.empty.insert x 

/-- Closure of a LTL formula. -/
def closure [BEq p] [Hashable p] (f : LTLFormula p) : Std.HashSet (LTLFormula p) :=
  let sf := (subformulas f).insert tru
  hashSetUnion sf (hashSetMap neg' sf)

/-- `elementary` checks whether a subset of `closure f` is elementary. -/
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

/-- The type of elementary subsets. -/
def ElemState [BEq p] [Hashable p] (f : LTLFormula p) := { hs : Std.HashSet (Subset (closure f)) // elementary hs }

instance [BEq p] [Hashable p] {f : LTLFormula p} : BEq (ElemState f) where
  beq x y := x.val == y.val

instance [BEq p] [Hashable p] {f : LTLFormula p} : Hashable (ElemState f) where
  hash x := hash x.val

instance [BEq p] [Hashable p] [Repr p] {f : LTLFormula p} : Repr (ElemState f) where
  reprPrec x := reprPrec x.val

/-- Enumeration of all elementary subsets. -/
def elemStates [BEq p] [Hashable p] (f : LTLFormula p) : Array (ElemState f) :=
  (subsets (closure f)).filterMap (fun s => match decEq (elementary s) true with
    | isTrue h => some ⟨s, h⟩
    | isFalse _ => none)

/-- Atomic propositions of a given elementary subset. -/
def elemAtoms [BEq p] [Hashable p] {f : LTLFormula p} (s : ElemState f) : Std.HashSet (Subset (atoms f))
  := s.val.fold (fun hs f' => if let prim p' := f'.val then
      match decEq ((atoms f).contains p') true with
      | isTrue h => hs.insert ⟨p', h⟩
      | isFalse _ => hs
      else hs) {}

/-- A predicate for starting states of LTL-to-Buchi. -/
def isStart [BEq p] [Hashable p] {f : LTLFormula p} (e : ElemState f) : Bool :=
  contains' e.val f

/-- A transition predicate for LTL-to-Buchi. -/
def isNext [BEq p] [Hashable p] {f : LTLFormula p} (e e' : ElemState f) : Bool :=
  let cl := (closure f).toArray
  cl.all (fun nx => if let next x := nx then
    (contains' e.val nx) == (contains' e'.val x) else true)
  && cl.all (fun xy => if let untl x y := xy then
    (contains' e.val xy) == (contains' e'.val y || (contains' e'.val x && contains' e'.val xy)) else true)

/-- Final states of LTL-to-Buchi translation. -/
def buchiLTLFinal [BEq p] [Hashable p] (f : LTLFormula p) : Array (Option (ElemState f) → Bool) :=
  (closure f).toArray.filterMap (fun xy => if let untl x y := xy then
    some (fun st => if let some st := st then contains' st.val y || not (contains' st.val xy) else false) else none)

/-- Translation of a LTL formula to a GBA. -/
def gbuchiOfLTL [BEq p] [Hashable p] (f : LTLFormula p)
  : GeneralizedBuchiAutomata (Option (ElemState f)) (Std.HashSet (Subset (atoms f))) where
  init := #[none] --
  next := let es := elemStates f
    fun
      | some s => (es.filter (isNext s)).map (fun s' => (elemAtoms s', s'))
      | none => (es.filter isStart).map (fun s' => (elemAtoms s', s'))
  final := (buchiLTLFinal f).back?.getD (fun _ => false)
  finals := (buchiLTLFinal f).pop

/-- `checkProperty` checks whether the transition system `ts` satisfies LTL property `f`. -/
def checkProperty [BEq s] [Hashable s] [BEq p] [Hashable p]
  (ts : TransitionSystem s a p) (f : LTLFormula p) : Bool :=
  let bu := buchiOfTS (restrictProp ts (atoms f))
  let bu' := buchiOfGBuchi (gbuchiOfLTL (neg f))
  isEmpty (buchiOfGBuchi (buchiProd bu bu'))
