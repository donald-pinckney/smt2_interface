import Smt2.Syntax

@[reducible] def Smt2.Builder := EStateM String (List Smt2.cmd)

instance Smt2.Builder.Monad : Monad Smt2.Builder := inferInstance

-- meta def Smt2.Builder.to_format {α : Type} (build : Smt2.Builder α) : format :=
-- format.join $ List.intersperse "\n" $ (List.map to_fmt $ (build.run.run []).snd).reverse

def Smt2.Builder.run {α : Type} (build : Smt2.Builder α) : (EStateM.Result String (List Smt2.cmd) α) := EStateM.run build []
-- state_t.run (except_t.run build) []

def Smt2.Builder.fail {α : Type} : String → Smt2.Builder α := fun msg => EStateM.throw msg

-- meta instance (α : Type) : has_to_format (Smt2.Builder α) :=
-- ⟨ Smt2.Builder.to_format ⟩

namespace Smt2

namespace Builder

def sort.bool : sort := "Bool"
def sort.int : sort := "Int"
def sort.array (dom cod : sort) : sort := sort.apply "Array" [dom, cod]
def sort.set   (dom : sort) : sort := sort.apply "Set" [dom]


def equals (t u : term) : term :=
term.apply "=" [t, u]

def not (t : term) : term :=
term.apply "not" [t]

def implies (t u : term) : term :=
term.apply "=>" [t, u]

def forallq (sym : symbol) (s : sort) (t : term) : term :=
term.forallq [(sym, s)] t

def and (ts : List term) : term :=
term.apply "and" ts

def and2 (t u : term) : term :=
and [t, u]

def or (ts : List term) : term :=
term.apply "or" ts

def or2 (t u : term) : term :=
or [t, u]

def xor (ts : List term) : term :=
term.apply "xor" ts

def xor2 (t u : term) : term :=
xor [t, u]

def iff (t u : term) : term :=
term.apply "iff" [t, u]

def lt (t u : term) : term :=
term.apply "<" [t, u]

def lte (t u : term) : term :=
term.apply "<=" [t, u]

def gt (t u : term) : term :=
term.apply ">" [t, u]

def gte (t u : term) : term :=
term.apply ">=" [t, u]

def add (t u : term) : term :=
term.apply "+" [t, u]

def sub (t u : term) : term :=
term.apply "-" [t, u]

def mul (t u : term) : term :=
term.apply "*" [t, u]

def div (t u : term) : term :=
term.apply "div" [t, u]

def mod (t u : term) : term :=
term.apply "mod" [t, u]

def neg (t : term) : term :=
term.apply "-" [t]

def ite (c t f : term) : term :=
term.apply "ite" [c, t, f]

def int_lit (i : Int) : term :=
term.lit $ literal.number i

def bool_lit (b : Bool) : term :=
term.lit $ literal.bool b

def var (x : symbol) : term :=
term.qual_id $ qualified_name.id x

def select (arr : term) (idx : term) : term :=
term.apply "select" [arr, idx]

def store (arr : term) (idx : term) (val : term) : term :=
term.apply "store" [arr, idx, val]

-- Begin bitvec operations
def bv_const (bitwidth:Nat) (i : Int) : term :=
term.lit $ literal.bitvec bitwidth i

def bv_add (t u : term) : term :=
term.apply "bvadd" [t, u]

def bv_sub (t u : term) : term :=
term.apply "bvsub" [t, u]

def bv_mul (t u : term) : term :=
term.apply "bvmul" [t, u]

def bv_udiv (t u : term) : term :=
term.apply "bvudiv" [t, u]

def bv_sdiv (t u : term) : term :=
term.apply "bvsdiv" [t, u]

def bv_urem (t u : term) : term :=
term.apply "bvurem" [t, u]

def bv_smod (t u : term) : term :=
term.apply "bvsmod" [t, u]

def bv_srem (t u : term) : term :=
term.apply "bvsrem" [t, u]

def bv_or (t u : term) : term :=
term.apply "bvor" [t, u]

def bv_and (t u : term) : term :=
term.apply "bvand" [t, u]

def bv_xor (t u : term) : term :=
term.apply "bvxor" [t, u]

def bv_shl (t u : term) : term :=
term.apply "bvshl" [t, u]

def bv_lshr (t u : term) : term :=
term.apply "bvlshr" [t, u]

def bv_ashr (t u : term) : term :=
term.apply "bvashr" [t, u]

def bv_sle (t u : term) : term :=
term.apply "bvsle" [t, u]

def bv_slt (t u : term) : term :=
term.apply "bvslt" [t, u]

def bv_ule (t u : term) : term :=
term.apply "bvule" [t, u]

def bv_ult (t u : term) : term :=
term.apply "bvult" [t, u]

def bv_zext (bitsz : Nat) (t : term) : term :=
term.apply2 (term.apply "_"
    [term.qual_id "zero_extend", term.lit bitsz])
    [t]

def bv_sext (bitsz : Nat) (t : term) : term :=
term.apply2 (term.apply "_"
    [term.qual_id "sign_extend", term.lit bitsz])
    [t]

def bv_extract (upper lower : Nat) (t : term) : term :=
term.apply2 (term.apply "_" [term.qual_id "extract",
    term.lit ↑upper, term.lit ↑lower])
    [t]
-- End bitvec operations

def add_command (c : cmd) : Builder Unit := do
let cs ← EStateM.get
EStateM.set (c :: cs)

def echo (msg : String) : Builder Unit :=
add_command (cmd.echo msg)

def check_sat : Builder Unit :=
add_command cmd.check_sat

def pop (n : Nat) : Builder Unit :=
add_command $ cmd.pop n

def push (n : Nat) : Builder Unit :=
add_command $ cmd.push n

def scope {α} (level : Nat) (action : Builder α) : Builder α :=
do 
    push level
    let res ← action
    pop level
    return res

def assert (t : term) : Builder Unit :=
add_command $ cmd.assert_cmd t

def reset : Builder Unit :=
add_command cmd.reset

def exit' : Builder Unit :=
add_command cmd.exit_cmd

def declare_const (sym : String) (s : sort) : Builder Unit :=
add_command $ cmd.declare_const sym s

def declare_fun (sym : String) (ps : List sort) (ret : sort) : Builder Unit :=
add_command $ cmd.declare_fun sym ps ret

def declare_sort (sym : String) (arity : Nat) : Builder Unit :=
add_command $ cmd.declare_sort sym arity

end Builder

end Smt2
