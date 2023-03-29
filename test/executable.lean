import Smt2

def mustBeSAT (b : Smt2.Builder Unit) : IO Unit := do
  let r ← smt2 b
  match r with 
  | .sat => return ()
  | _ => 
    IO.eprintln s!"Expected SAT, got {r}"
    IO.Process.exit 1

def mustBeUNSAT (b : Smt2.Builder Unit) : IO Unit := do
  let r ← smt2 b 
  match r with 
  | .unsat => return ()
  | _ =>  
    IO.eprintln s!"Expected UNSAT, got {r}"
    IO.Process.exit 1

open Smt2.Builder

def main : IO Unit := do
  mustBeSAT ( do
    assert $ bool_lit true
    check_sat
  )

  mustBeUNSAT ( do
    assert $ bool_lit false
    check_sat
  )

  mustBeSAT ( do
    declare_const "x" sort.bool
    declare_const "y" sort.bool
    assert $ equals (var "x") (var "y")
    check_sat
  )

  mustBeUNSAT ( do
    declare_const "x" sort.bool
    assert $ equals (var "x") (not (var "x"))
    check_sat
  )


-- def checkSAT ()