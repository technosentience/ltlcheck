import Ltlcheck.Util

/-- Base structure for automata. `s` denotes states, `a` actions. -/
structure BaseAutomata (s a : Type u) where
  init : Array s
  next : s → Array (a × s)

/-- Transition system, adds a type of elementary propositions `p`. -/
structure TransitionSystem (s a p : Type u) extends BaseAutomata s a where
  prop : s → Array p

/-- Buchi automata, has final states (defined as a predicate for convenience). -/
structure BuchiAutomata (s a : Type u) extends BaseAutomata s a where
  final : s → Bool

/-- Generalized Buchi automata. Has additional sets of final states. -/
structure GeneralizedBuchiAutomata (s a : Type u) extends BuchiAutomata s a where
  finals : Array (s → Bool) 

/-- Helper final states function for GBAs.
This way, the set F of groups of final states is nonempty by construction. -/
def gbaFinal (gba : GeneralizedBuchiAutomata s a) (s' : s) : Fin gba.finals.size.succ → Bool
  | ⟨0, _⟩ => gba.final s'
  | ⟨n + 1, h⟩ => gba.finals.get ⟨n, Nat.le_of_succ_le_succ h⟩ s'

/-- TS-to-Buchi conversion -/
def buchiOfTS [BEq p] [Hashable p] (ts : TransitionSystem s a p)
  : BuchiAutomata (Option s) (Std.HashSet p) where
  init := #[none]
  next := fun
    | some s' => (ts.next s').map (fun (_, s') => (hashSetOfArray (ts.prop s'), some s'))
    | none => ts.init.map (fun s' => (hashSetOfArray (ts.prop s'), some s'))
  final := fun _ => true

/-- Product of Buchi Automata -/
def buchiProd [BEq a] (ba₁ : BuchiAutomata s₁ a) (ba₂ : BuchiAutomata s₂ a)
  : GeneralizedBuchiAutomata (s₁ × s₂) a where
  init := arrayProd ba₁.init ba₂.init
  next := fun (s'₁, s'₂) => arrayZipProd (ba₁.next s'₁) (ba₂.next s'₂)
  final := fun (s', _) => ba₁.final s'
  finals := #[fun (_, s') => ba₂.final s']

/-- GBA-to-BA conversion -/
def buchiOfGBuchi (gba : GeneralizedBuchiAutomata s a)
  : BuchiAutomata (s × Fin gba.finals.size.succ) a where
  init := gba.init.map (·, 0)
  next := fun (s', n) => (gba.next s').map (fun (a, sn) => (a, sn, n + if gbaFinal gba sn n then 1 else 0))
  final := fun (s', n) => n == 0 && gba.final s'

/-- Set of all states reachable from a set of states. -/
def reachableFrom [BEq s] [Hashable s] (next : s → Array s) (init : Array s) : Array s
  := Id.run $ do
    let mut q := init
    let mut v := Std.HashSet.empty
    while !q.isEmpty do
      if let some x := q.back? then
      q := q.pop
      if !v.contains x then
        q := q.append (next x)
        v := v.insert x
    return v.toArray

/-- `isEmpty` checks whether the language accepted by a given Buchi automata is empty. -/
def isEmpty [BEq s] [Hashable s] (ba : BuchiAutomata s a) : Bool :=
  let next' s' := (ba.next s').map Prod.snd
  reachableFrom next' ba.init
  |> Array.filter ba.final
  |> Array.filter (fun s' => (reachableFrom next' (next' s')).contains s')
  |> Array.isEmpty

/-- Handshake product of two transition systems. Set of handshake actions `hs` is a predicate for convenience. -/
def handshake [BEq a] (ts₁ : TransitionSystem s₁ a p) (ts₂ : TransitionSystem s₂ a p)
  (hs : a → Bool) : TransitionSystem (s₁ × s₂) a p where
  init := arrayProd ts₁.init ts₂.init
  next := fun (x₁, x₂) =>
    let (h₁, nh₁) := Array.partition (hs ∘ Prod.fst) (ts₁.next x₁)
    let (h₂, nh₂) := Array.partition (hs ∘ Prod.fst) (ts₂.next x₂)
    nh₁.map (fun (a, x') => (a, x', x₂))
    ++ nh₂.map (fun (a, x') => (a, x₁, x'))
    ++ arrayZipProd h₁ h₂
  prop := fun (x₁, x₂) => ts₁.prop x₁ ++ ts₂.prop x₂

/-- Interleaving product of two transition systems. -/
def interleave [BEq a] (ts₁ : TransitionSystem s₁ a p) (ts₂ : TransitionSystem s₂ a p)
  : TransitionSystem (s₁ × s₂) a p := handshake ts₁ ts₂ (fun _ => false)

/-- Helper function for restricting the set of propositions of a TS. -/
def restrictProp [BEq p] [Hashable p] (ts : TransitionSystem s a p)
  (ps : Std.HashSet p) : TransitionSystem s a (Subset ps) where
  init := ts.init
  next := ts.next
  prop s' := ts.prop s' |> Array.filterMap
    (fun p' => match decEq (ps.contains p') true with
      | isTrue h => some ⟨p', h⟩
      | isFalse _ => none)
