import Ltlcheck.Syntax

-- Train states.
inductive S₁
  | far | near | inside
deriving BEq, Hashable, Repr

-- Gate states.
inductive S₂
 | up | down
deriving BEq, Hashable, Repr

-- Controller states.
inductive S₃
  | ze | on | tw | th
deriving BEq, Hashable, Repr

-- All actions.
inductive Act
  | approach | enter | exit | lower | raise
deriving BEq, Hashable, Repr

-- All elementary propositions.
inductive Pr
  | far | near | inside | up | down
deriving BEq, Hashable, Repr

-- The train system.
def TS₁ : TransitionSystem S₁ Act Pr where
  init := #[S₁.far]
  next := fun
    | S₁.far => #[(Act.approach, S₁.near)]
    | S₁.near => #[(Act.enter, S₁.inside)]
    | S₁.inside => #[(Act.exit, S₁.far)]
  prop := fun
    | S₁.far => #[Pr.far]
    | S₁.near => #[Pr.near]
    | S₁.inside => #[Pr.inside]

-- The gate system.
def TS₂ : TransitionSystem S₂ Act Pr where
  init := #[S₂.up]
  next := fun
    | S₂.up => #[(Act.lower, S₂.down)]
    | S₂.down => #[(Act.raise, S₂.up)]
  prop := fun
    | S₂.up => #[Pr.up]
    | S₂.down => #[Pr.down]

-- The controller system.
def TS₃ : TransitionSystem S₃ Act Pr where
  init := #[S₃.ze]
  next := fun
    | S₃.ze => #[(Act.approach, S₃.on)]
    | S₃.on => #[(Act.lower, S₃.tw)]
    | S₃.tw => #[(Act.exit, S₃.th)]
    | S₃.th => #[(Act.raise, S₃.ze)]
  prop _ := #[]

-- The train-gate-controller system
def TS :=
  let ts' := handshake TS₃ TS₁ #[Act.approach, Act.exit].contains
  handshake ts' TS₂ #[Act.lower, Act.raise].contains

-- G !(inside && down)
def F1 : LTLFormula Pr := [LTL| G ¬ (#Pr.inside ∧ #Pr.down)]

-- G (near -> F down)
def F2 : LTLFormula Pr := [LTL| G (#Pr.near → F #Pr.down)]

-- G (inside -> X far)
def F3 : LTLFormula Pr := [LTL| G (#Pr.inside → X #Pr.far)]

#eval checkProperty TS F1 -- false
#eval checkProperty TS F2 -- true
#eval checkProperty TS F3 -- false
