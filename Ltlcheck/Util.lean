import Std.Data.HashSet

instance : Hashable PUnit where
  hash _ := 37

instance [BEq α] [Hashable α] : BEq (Std.HashSet α) where
  beq a b := a.toArray.all b.contains && b.toArray.all a.contains

instance [BEq α] [Hashable α] : Hashable (Std.HashSet α) where
  hash a := (a.toArray.map hash).foldl Xor.xor 0  -- not ideal but works

instance [BEq α] [Hashable α] [Repr α] : Repr (Std.HashSet α) where
  reprPrec hs := reprPrec hs.toArray

def hashSetOfArray [BEq α] [Hashable α] (as : Array α) : Std.HashSet α
  := as.foldl Std.HashSet.insert Std.HashSet.empty

def hashSetUnion [BEq α] [Hashable α] (hs₁ hs₂ : Std.HashSet α) : Std.HashSet α
  := hs₁.fold Std.HashSet.insert hs₂

def hashSetMap [BEq α] [Hashable α] [BEq β] [Hashable β] (f : α → β) (hs : Std.HashSet α) : Std.HashSet β
  := hs.fold (fun h a => Std.HashSet.insert h (f a)) Std.HashSet.empty

def arrayProd (as : Array α) (bs : Array β) : Array (α × β)
  := Id.run $ do
    let mut pr := #[]
    for a in as do
      for b in bs do
        pr := pr.push (a, b)
    pr

def arrayZipProd [BEq γ] (as : Array (γ × α)) (bs : Array (γ × β)) : Array (γ × α × β)
  := Id.run $ do
    let mut pr := #[]
    for (c, a) in as do
      for (c', b) in bs do
        if c == c' then pr := pr.push (c, a, b)
    pr

def Subset [BEq α] [Hashable α] (hs : Std.HashSet α) := { a : α // hs.contains a }

instance [BEq α] [Hashable α] {hs : Std.HashSet α} : BEq (Subset hs) where
  beq a b := a.val == b.val

instance [BEq α] [Hashable α] {hs : Std.HashSet α} : Hashable (Subset hs) where
  hash a := hash a.val

instance [BEq α] [Hashable α] [Repr α] {hs : Std.HashSet α} : Repr (Subset hs) where
  reprPrec x := reprPrec x.val

def contains' [BEq α] [Hashable α] {hs : Std.HashSet α} (hs' : Std.HashSet (Subset hs)) (x : α)
  := match decEq (hs.contains x) true with
    | isTrue h => hs'.contains ⟨x, h⟩
    | isFalse _ => false

def insert' [BEq α] [Hashable α] {hs : Std.HashSet α} (hs' : Std.HashSet (Subset hs)) (x : α)
  := match decEq (hs.contains x) true with
    | isTrue h => hs'.insert ⟨x, h⟩
    | isFalse _ => hs'

def subsets [BEq α] [Hashable α] (hs : Std.HashSet α) : Array (Std.HashSet (Subset hs))
  := hs.fold (fun ss x => ss ++ ss.map (insert' · x)) #[Std.HashSet.empty]
