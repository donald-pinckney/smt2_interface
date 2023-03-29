namespace Smt2


@[reducible] def symbol : Type := String
@[reducible] def identifier : Type := String

inductive literal : Type
| number : Int → literal
| bitvec : Nat → Int → literal
| string : String → literal
| bool : Bool → literal
deriving Repr

-- def hexdigit (n:Nat) : Char :=
-- Char.ofNat $
--   if n < 10 then '0'.toNat + n
--   else 'A'.toNat + n - 10

-- def to_hex : Nat → String
-- | 0        => "" -- leave it as "".
-- | n'@(n+1) =>
--   have n' / 16 < n', begin apply nat.div_lt_self, apply nat.zero_lt_succ, comp_val end,
--   to_hex (n' / 16) ++ to_string (hexdigit (n' % 16))

def literal.to_string : literal → String
| (literal.number i)   => toString i
| (literal.string str) => str
| (literal.bitvec _bitsz _num) => "NYI"
  -- let unum := if num < 0 then 2^bitsz - num.nat_abs + 1 else num.to_nat in
  -- if bitsz % 4 = 0 then -- use #xNNNN format
  --   let l := to_hex unum in
  --   "#x" ++ list.as_string (list.repeat '0' (bitsz / 4 - l.length)) ++ l
  -- else -- use #bBBBB format
  --   let b     := ((nat.bits unum).map (λ b, cond b 1 0)).reverse in
  --   let zeros := list.repeat 0 (bitsz - list.length b) in
  --   let bits  := zeros ++ b in  -- Add leading zeros
  --   "#b" ++ bits.foldl (λ fmt bit, fmt ++ to_string bit) ""
| (literal.bool b) =>
    if b then "true" else "false"

def literal.to_format : literal → Std.Format :=
Std.ToFormat.format ∘ literal.to_string

instance literal_has_format : Std.ToFormat literal :=
⟨ literal.to_format ⟩

instance int_to_literal : Coe Int literal :=
⟨ literal.number ⟩

inductive sort : Type
| id : identifier → sort
| apply : identifier → List sort → sort
deriving BEq, Hashable, Repr

instance : Coe String sort :=
⟨ sort.id ⟩

mutual
  def sort.to_format : sort → Std.Format
  | (sort.id i) => Std.ToFormat.format i
  | (sort.apply name sorts) => -- (name sort1 sort2 ..)
    Std.Format.paren $
      Std.ToFormat.format name ++
      (Std.Format.join $ sort.to_format.list sorts)
  def sort.to_format.list : List sort -> List Std.Format
  | [] => []
  | s :: rest => (Std.ToFormat.format " " ++ sort.to_format s) :: (sort.to_format.list rest)
end

instance sort_has_to_fmt : Std.ToFormat sort :=
⟨ sort.to_format ⟩


inductive attr : Type
deriving Repr

inductive qualified_name : Type
| id : identifier → qualified_name
| qual_id : identifier → sort → qualified_name
deriving Repr

def qualified_name.to_format : qualified_name → Std.Format
| (qualified_name.id i) => i
| (qualified_name.qual_id _ _) => "NYI"

instance string_to_qual_name : Coe String qualified_name :=
    ⟨ fun str => qualified_name.id str ⟩

inductive term : Type
| qual_id : qualified_name → term
| lit : literal → term
| apply : qualified_name → List term → term
| apply2 : term → List term → term -- General form of `apply`
-- | letb : List (name × term) → term → term
| forallq : List (symbol × sort) → term → term
| existsq : List (symbol × sort) → term → term
| annotate : term → List attr → term
deriving Repr

instance qual_name_to_term : Coe qualified_name term :=
⟨ term.qual_id ⟩

instance literal_to_term : Coe literal term :=
⟨ term.lit ⟩

mutual
  def term.to_format : term → Std.Format
  | (term.qual_id id) => id.to_format
  | (term.lit spec_const) => spec_const.to_format
  | (term.apply qual_name ts) =>
      let formatted_ts := Std.Format.join $ List.intersperse " "  $ term.to_format.list ts
      Std.Format.paren (
          qual_name.to_format ++ Std.ToFormat.format " " ++ formatted_ts)
  | (term.apply2 f ts) =>
      let formatted_ts := Std.Format.join $ List.intersperse " "  $ term.to_format.list ts
      Std.Format.paren (
          f.to_format ++ Std.ToFormat.format " " ++ formatted_ts)
  -- | (term.letb ps ret) => "NYI"
  | (term.forallq bs body) =>
      "(forall (" ++
      Std.Format.join (bs.map (fun ⟨sym, sort⟩ => Std.Format.paren $ Std.ToFormat.format sym ++ " " ++ Std.ToFormat.format sort)) ++ ") " ++
      term.to_format body ++ ")"
  | (term.existsq _ps _ret) => "NYI existsq"
  | (term.annotate _ _) => "NYI annotate"
  def term.to_format.list : List term → List Std.Format
  | [] => []
  | x :: rest => (Std.ToFormat.format " " ++ term.to_format x) :: (term.to_format.list rest)
end

inductive fun_def : Type
inductive info_flag : Type
inductive keyword : Type
inductive option : Type

inductive cmd : Type
| assert_cmd : term → cmd
| check_sat : cmd
| check_sat_assuming : term → cmd -- not complete
| declare_const : symbol → sort → cmd
| declare_fun : symbol → List sort → sort → cmd
| declare_sort : symbol → Nat → cmd
| define_fun : fun_def → cmd
| define_fun_rec : fun_def → cmd
| define_funs_rec : cmd -- not complete
| define_sort : symbol → List symbol → sort → cmd
| echo : String → cmd
| exit_cmd : cmd
| get_assertions : cmd
| get_assignment : cmd
| get_info : info_flag → cmd
| get_model : cmd
| get_option : keyword → cmd
| get_proof : cmd
| get_unsat_assumtpions : cmd
| get_unsat_core : cmd
| get_value : cmd -- not complete
| pop : Nat → cmd
| push : Nat → cmd
| reset : cmd
| reset_assertions : cmd
| set_info : attr → cmd
| set_logic : symbol → cmd
| set_opt : option → cmd

open cmd

def string_lit (s : String) : Std.Format :=
Std.Format.bracket "\"" (Std.ToFormat.format s) "\""

def cmd.to_format : cmd → Std.Format
| (echo msg) => "(echo " ++ string_lit msg ++ ")\n"
| (declare_const sym srt) => "(declare-const " ++ sym ++ " " ++ Std.ToFormat.format srt ++ ")"
| (assert_cmd t) => "(assert " ++ t.to_format ++ ")"
| (check_sat) => "(check-sat)"
| (declare_fun sym ps rs) => "(declare-fun " ++ sym ++
    Std.Format.bracket " ("  (Std.Format.join $ List.intersperse " " $ List.map Std.ToFormat.format ps) ")" ++ " " ++ Std.ToFormat.format rs ++ ")"
| (declare_sort sym arity) => "(declare-sort " ++ sym ++ " " ++ toString arity ++ ")"
| (reset) => "(reset)"
| _ => "NYI"

instance : Std.ToFormat cmd :=
⟨ cmd.to_format ⟩

end Smt2
