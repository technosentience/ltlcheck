import Ltlcheck.Ltl

declare_syntax_cat ltl
syntax "⊤" : ltl
syntax "⊥" : ltl
syntax:120 "#" term:120 : ltl
syntax:60  ltl:60 "∧" ltl:61 : ltl
syntax:70  ltl:60 "∨" ltl:61 : ltl
syntax:50  ltl:51 "→" ltl:50 : ltl
syntax:49  ltl:50 "↔" ltl:51 : ltl
syntax:100 "¬" ltl:100 : ltl
syntax:100 "X" ltl:100 : ltl
syntax:100 ltl:100 "U" ltl:100 : ltl
syntax:100 ltl:100 "R" ltl:100 : ltl
syntax:100 "F" ltl:100 : ltl
syntax:100 "G" ltl:100 : ltl
syntax "(" ltl ")" : ltl

syntax "[LTL| " ltl "]" : term

macro_rules
  | `([LTL| ⊤]) => `(LTLFormula.tru)
  | `([LTL| ⊥]) => `(LTLFormula.fal)
  | `([LTL| # $t:term]) => `(LTLFormula.prim $t)
  | `([LTL| ¬ $x:ltl]) => `(LTLFormula.neg [LTL| $x])
  | `([LTL| X $x:ltl]) => `(LTLFormula.next [LTL| $x])
  | `([LTL| F $x:ltl]) => `(LTLFormula.fin [LTL| $x])
  | `([LTL| G $x:ltl]) => `(LTLFormula.glob [LTL| $x])
  | `([LTL| $x:ltl ∧ $y:ltl]) => `(LTLFormula.andf [LTL| $x] [LTL| $y])
  | `([LTL| $x:ltl ∨ $y:ltl]) => `(LTLFormula.orf [LTL| $x] [LTL| $y])
  | `([LTL| $x:ltl → $y:ltl]) => `(LTLFormula.impl [LTL| $x] [LTL| $y])
  | `([LTL| $x:ltl ↔ $y:ltl]) => `(LTLFormula.eqv [LTL| $x] [LTL| $y])
  | `([LTL| $x:ltl U $y:ltl]) => `(LTLFormula.untl [LTL| $x] [LTL| $y])
  | `([LTL| $x:ltl R $y:ltl]) => `(LTLFormula.rls [LTL| $x] [LTL| $y])
  | `([LTL| ($x:ltl)]) => `([LTL| $x])
