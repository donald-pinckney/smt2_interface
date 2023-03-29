import Init.System.IO
import Smt2.Builder
import Smt2.Syntax
import Smt2.Z3

inductive Smt2.response : Type
| sat
| unsat
| unknown
| other (str : String) : Smt2.response
deriving Repr

instance : ToString Smt2.response where
  toString : Smt2.response -> String
    | .sat => "SAT"
    | .unsat => "UNSAT"
    | .unknown => "UNKNOWN"
    | .other str => s!"other: {str}"

def parse_Smt2_result (str : String) : Smt2.response :=
-- Removes trailing white space.
/- carriage return -/
let str := List.asString $ (str.toList.reverse.dropWhile (λ (c:Char) => c.isWhitespace ∨ c.toNat = 13)).reverse

if str = "sat" then 
  Smt2.response.sat
else if str = "unsat" then 
  Smt2.response.unsat
else if str = "unknown" then 
  Smt2.response.unknown
else 
  Smt2.response.other str

def cmds_to_string (cmds : List Smt2.cmd) : String :=
toString $ Std.Format.join $ List.intersperse "\n" $ List.map (λ c => Std.ToFormat.format c) cmds.reverse


def smt2 (build : Smt2.Builder Unit) (log_query : Option String := none) : IO Smt2.response :=
do 
    -- let z3 ← z3_instance.start
    let build_result := build.run
    match build_result with
    | .error err _ => do 
        IO.eprintln $ "builder failed with: " ++ err
        IO.Process.exit 1
    | .ok _ cmds => do
        let query := cmds_to_string cmds

        -- IO.println "maybe making log file"
        (
          match log_query with
          | none => return ()
          | some log_path => do
              let file ← IO.FS.Handle.mk log_path IO.FS.Mode.write
              IO.FS.Handle.putStrLn file query
        )

        -- IO.println "z3.raw starting"
        let res ← z3_instance.raw query
        -- z3.stop
        return parse_Smt2_result res
