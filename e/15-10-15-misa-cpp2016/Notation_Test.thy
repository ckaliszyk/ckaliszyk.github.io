(* This file does not correspond to any real Mizar article,
   it is only there to test whether the Mizar theory defines the
   Isar innsr syntax notations correctly *)
theory Notation_Test
imports Xboole_0
begin

consts
  element :: "s => ty" ("( Element of _ )" 105)
  onto :: ty
  even :: ty
  Function :: ty

text_raw {*\DefineSnippet{notationtest1}{*}
term "x is set"
term "x is empty set"
term "x is non empty Element of NAT"
term "x is empty non onto Function"
term "the empty set"
text_raw {*}%EndSnippet*}
text_raw {*\DefineSnippet{notationtest2}{*}
term "P & Q iff Z implies (not P implies R or W)"
term "for x,y being set,z being object holds P(x,y,z)"
term "ex y being even Element of NAT st Q(y)"
term "P provided Q"
text_raw {*}%EndSnippet*}

end
