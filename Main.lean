import Ltlcheck

def main : IO Unit := do
  IO.println s!"TS wrt property 1: {checkProperty TS F1}!"
  IO.println s!"TS wrt property 2: {checkProperty TS F2}!"
  IO.println s!"TS wrt property 3: {checkProperty TS F3}!"
