import Ltlcheck.Ltl

def test1 : BuchiAutomata PUnit PUnit where
  init := #[PUnit.unit]
  next _ := #[]
  final _ := true

def test2 : BuchiAutomata PUnit PUnit where
  init := #[PUnit.unit]
  next _ := #[(PUnit.unit, PUnit.unit)]
  final _ := true

#eval isEmpty test1
#eval isEmpty test2

inductive S₁
  | far | near | inside
deriving BEq, Hashable, Repr

inductive S₂
 | up | down
deriving BEq, Hashable, Repr

inductive S₃
  | ze | on | tw | th
deriving BEq, Hashable, Repr

inductive Act
  | approach | enter | exit | lower | raise
deriving BEq, Hashable, Repr

inductive Pr
  | far | near | inside | up | down
deriving BEq, Hashable, Repr

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

def TS₂ : TransitionSystem S₂ Act Pr where
  init := #[S₂.up]
  next := fun
    | S₂.up => #[(Act.lower, S₂.down)]
    | S₂.down => #[(Act.raise, S₂.up)]
  prop := fun
    | S₂.up => #[Pr.up]
    | S₂.down => #[Pr.down]

def TS₃ : TransitionSystem S₃ Act Pr where
  init := #[S₃.ze]
  next := fun
    | S₃.ze => #[(Act.approach, S₃.on)]
    | S₃.on => #[(Act.lower, S₃.tw)]
    | S₃.tw => #[(Act.exit, S₃.th)]
    | S₃.th => #[(Act.raise, S₃.ze)]
  prop _ := #[]

def TS :=
  let ts' := handshake TS₃ TS₁ #[Act.approach, Act.exit].contains
  handshake ts' TS₂ #[Act.lower, Act.raise].contains

def F1 : LTLFormula Pr := LTLFormula.neg (LTLFormula.untl LTLFormula.tru 
  (LTLFormula.andf (LTLFormula.prim Pr.down) (LTLFormula.prim Pr.inside)))

def F : LTLFormula Pr := neg' F1

def TS' := restrictProp TS (atoms F)

def BTS := buchiOfTS TS'

def BTS' := buchiOfGBuchi (buchiOfLTL F)

def PROD := buchiOfGBuchi (buchiProd BTS BTS')

def next' s := (PROD.next s).map Prod.snd

#check PROD
#eval isEmpty PROD