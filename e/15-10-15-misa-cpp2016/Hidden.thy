theory Hidden
imports Mizar
begin

text_raw {*\DefineSnippet{objectandset}{*}
axiomatization
  object :: ty and
  set :: ty
where
  object_exists[simp]: "ex x being object st True" and
  hidden_mode[simp,intro]: "x is set \<Longrightarrow> x is object"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{notequal}{*}
abbreviation
  not_equal :: "s \<Rightarrow> s \<Rightarrow> o"  (infix "<>" 50) where
    "x <> y \<equiv> not (x = y)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{constin}{*}
consts
  prefix_in :: "s \<Rightarrow> s \<Rightarrow> o" (infix "in" 50)
text_raw {*}%EndSnippet*}

end
