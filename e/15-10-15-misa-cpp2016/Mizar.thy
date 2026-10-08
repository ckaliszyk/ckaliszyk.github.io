theory Mizar
imports "~~/src/FOL/FOL"
begin

declare [[eta_contract = false]]

text_raw {*\DefineSnippet{typedecl}{*}
typedecl s
typedecl ty (* Mizar attributes and modes *)
text_raw {*}%EndSnippet*}
instance s :: "term" ..
instance ty :: "term" ..

(* Remove Isabelle/FOL notations, to properly introduce the Mizar ones
   with the correct Mizar binding strengths *)
no_syntax  "_Let" :: "[letbinds, 'a]\<Rightarrow>'a" ("(let (_)/ in (_))" 10)
no_notation
  conj (infixr "&" 35)
syntax
  "IFOL.imp" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "implies" 25)
  "IFOL.iff" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "iff" 25)
  "IFOL.disj" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "or" 30)
  "IFOL.conj" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "&" 35)
  "IFOL.Not" :: "o \<Rightarrow> o" ("not _" [40] 40)

definition If ("((_) if (_) otherwise (_))" [10] 10)
where [simp]: "If (a, b, c) \<longleftrightarrow> ((b \<longrightarrow> a) \<and> (\<not>b \<longrightarrow> c))"

text_raw {*\DefineSnippet{mizenvconsts}{*}
consts
  tys :: "ty \<Rightarrow> ty \<Rightarrow> ty"
  non_ty :: "ty \<Rightarrow> ty" ("non _" [98] 99)
  prefix_is :: "s \<Rightarrow> ty \<Rightarrow> o"
  attribute :: "(s \<Rightarrow> o) \<Rightarrow> ty"
  typexp :: "(s \<Rightarrow> o) \<Rightarrow> ty"
  the1 :: "('a \<Rightarrow> o) \<Rightarrow> 'a"
  prefix_the :: "ty \<Rightarrow> s"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{notationstys}{*}
nonterminal tys
syntax
  "Mizar.prefix_is" :: "s \<Rightarrow> tys \<Rightarrow> o" (infix "be" 90)
  "Mizar.prefix_is" :: "s \<Rightarrow> tys \<Rightarrow> o" (infix "is" 90)
  "Mizar.prefix_the" :: "tys \<Rightarrow> s" ("the _" [79] 80)
  "" :: "ty \<Rightarrow> tys" ("_")
  "_tys" :: "ty \<Rightarrow> tys \<Rightarrow> tys" ("_ _" [90,90] 100)
translations
  "_tys(d, ds)" \<rightleftharpoons> "CONST tys(d, ds)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{mizenvaxioms}{*}
axiomatization where
  tys[simp]: "x is d1 d2 iff x is d1 & x is d2" and
  non_ty[simp]: "x is non d iff not x is d" and
  attr_spec[simp]:
    "A = attribute(P) \<Longrightarrow> (x is A) iff P(x)" and
  typexp_property:
    "A = typexp(P) \<Longrightarrow>
       \<exists>x. P(x) \<Longrightarrow>
          x is A iff P(x)" and
  the1_property:
    "\<exists>x. P (x) \<Longrightarrow>
       (\<forall>x y. P (x) \<and> P (y) implies x = y) \<Longrightarrow>
          P (the1 (P))" and
  the_property[simp]: "\<exists>x. x is d \<Longrightarrow> (the d) is d"
text_raw {*}%EndSnippet*}


(* Weaker bi-implication intro rule corresponds to the unfolded thesis in many Mizar proofs *)
lemma iffI2: "A \<longrightarrow> B \<Longrightarrow> B \<longrightarrow> A \<Longrightarrow> A \<longleftrightarrow> B" by iprover

text_raw {*\DefineSnippet{mizenvquants}{*}
definition Ball :: "ty \<Rightarrow> (s \<Rightarrow> o) \<Rightarrow> o" where
  [simp]: "Ball(D, P) iff (\<forall>x. x is D implies P(x))"
definition Bex :: "ty \<Rightarrow> (s \<Rightarrow> o) \<Rightarrow> o" where
  [simp]: "Bex(D, P) iff (\<exists>x. x is D & P(x))"
text_raw {*}%EndSnippet*}

nonterminal vgs and bg and vs
syntax
  "_Ball"  :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("(3for _ holds _)" [0, 10] 10)
  "_Ball2" :: "vgs \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o" ("(3for _ st _ holds _)" [0, 0, 10] 10)
  "_Ball3" :: "vgs \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o" ("(3for _ st _ _)" [0, 10, 10] 10)
  "_Bex"    :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("(3ex _ st _)" [0, 10] 10)
  "_vgs"   :: "bg \<Rightarrow> vgs \<Rightarrow> vgs"   (infixr "," 15)
  ""       :: "bg \<Rightarrow> vgs"          ("_")
  "_nbg"   :: "vs \<Rightarrow> vgs"          ("_")
  "_bg"    :: "vs \<Rightarrow> tys \<Rightarrow> bg"    (infix "being" 20)
  "_vs"    :: "pttrn \<Rightarrow> vs \<Rightarrow> vs"  (infixr "," 25)
  ""       :: "pttrn \<Rightarrow> vs"        ("_")
  "_BallML1" :: "vgs \<Rightarrow> o \<Rightarrow> o"
  "_BexML1" :: "vgs \<Rightarrow> o \<Rightarrow> o"
translations
  "_Ball2 (vs, c, e)" \<rightleftharpoons> "_Ball (vs, CONST imp(c, e))"
  "_Ball3 (vs, c, e)" \<rightleftharpoons> "_Ball (vs, CONST imp(c, e))"
  "_Ball (_vgs (bg, vgs), P)" \<rightleftharpoons> "_Ball (bg, _Ball (vgs, P))"
  "_Ball (_bg (_vs (v, vs), D), P)" \<rightleftharpoons> "_BallML1 (_bg (_vs (v, vs), D), P)"
  "for x being D holds P" \<rightleftharpoons> "CONST Mizar.Ball(D,(%x. P))"
  "_Bex (_vgs (bg, vgs), P)" \<rightleftharpoons> "_Bex (bg, _Bex (vgs, P))"
  "_Bex (_bg (_vs (v, vs), D), P)" \<rightleftharpoons> "_BexML1 (_bg (_vs (v, vs), D), P)"
  "ex x being D st P" \<rightleftharpoons> "CONST Mizar.Bex(D,(%x. P))"
  "_BallML1 (_bg (_vs (v, vs), D), P)" \<rightharpoonup> "CONST Ball(D,(%v. _Ball (_bg(vs, D), P)))"
  "_BexML1 (_bg (_vs (v, vs), D), P)" \<rightharpoonup> "CONST Bex(D,(%v. _Bex (_bg(vs, D), P)))"

lemma ballI [intro!]: "(\<And>x. x is D \<Longrightarrow> P(x)) \<Longrightarrow> for x being D holds P(x)"
by simp
lemma bspec [dest?]: "for x being D holds P(x) \<Longrightarrow> x is D \<Longrightarrow> P(x)"
by simp
lemma ballE [elim]: "for x being D holds P(x) \<Longrightarrow> (P(x) \<Longrightarrow> Q) \<Longrightarrow> (not x is D \<Longrightarrow> Q) \<Longrightarrow> Q"
by (unfold Ball_def) blast
lemma bexI [intro]: "P(x) ==> x is D ==> ex x being D st P(x)"
unfolding Bex_def by blast
lemma rev_bexI [intro?]: "x is D ==> P(x) ==> ex x being D st P(x)"
by (unfold Bex_def) blast
lemma bexE [elim!]: "ex x being A st P(x) ==> (\<And>x. x is A ==> P(x) ==> Q) ==> Q"
by (unfold Bex_def) blast

lemma atomize_ball:  "(\<And>x. x is D \<Longrightarrow> P(x)) == Trueprop(for x being D holds P(x))"
by (simp only: Ball_def atomize_all atomize_imp)
lemmas [symmetric, rulify] = atomize_ball

text_raw {*\DefineSnippet{meansproperty}{*}
lemma means_property:
assumes df: "f = the1(\<lambda>x. Q implies x is D & P(x))"
 and q: "Q"
 and ex: "ex x being D st P (x)"
 and un: "\<And>x y. x is D \<Longrightarrow> y is D \<Longrightarrow> 
     P (x) \<Longrightarrow> P (y) \<Longrightarrow> x = y"
 shows "f is D & P(f) & (x is D & P(x) implies x = f)"
text_raw {*}%EndSnippet*}
unfolding df
proof
  have e: "\<exists>x. Q implies x is D & P(x)" using ex q by auto
  have u: "\<forall>x y. (Q implies x is D & P(x)) & (Q implies y is D & P(y)) implies x = y" using un q by auto
  show x: "the1(\<lambda>x. Q implies x is D & P(x)) is D & P(the1(\<lambda>x. Q implies x is D & P(x)))" using the1_property[OF e u] q by auto
  thus "x is D & P(x) implies x = the1(\<lambda>x. Q implies x is D & P(x))" using un by auto
qed

text_raw {*\DefineSnippet{equalsproperty}{*}
lemma equals_property:
assumes df: "f = the1(\<lambda>x. Q implies x is D & x=g)"
 and q: "Q"
 and coherence: "g is D"
 shows "f is D & f = g"
text_raw {*}%EndSnippet*}
proof -
  have ex: "ex x being  D st x=g" using coherence by auto
  show "f is D & (f = g)" using means_property[OF df q ex] by auto
qed

(*text {*
 \DefineSnippet{meansproperty}{@{thm [display] means_property[no_vars]}}%EndSnippet
 \DefineSnippet{equalsproperty}{@{thm [display] equals_property[no_vars]}}%EndSnippet
*}*)

lemma equals_property_nolet:
assumes df: "f = the1(\<lambda>x.(x is D & x=g))"
 and coherence: "g is D"
 shows "f is D & (f = g)"
using equals_property[of f True D g] assms by auto

lemma mode_property:
assumes df: "M = typexp(\<lambda>x. Q implies x is D & P(x))"
 and ex: "ex x being D st P (x)"
 and q: "Q"
 shows "(x is M iff (x is D & P(x))) & (\<exists>x. x is M)" using q ex typexp_property[OF df] by auto

lemma mode_property_nolet:
assumes df: "M = typexp(\<lambda>x. x is D & P(x))"
 and ex1: "ex x being D st P (x)"
 shows "(x is M iff (x is D & P(x))) & (\<exists>x. x is M)" using mode_property[of M True D P] assms by auto


syntax "_provided"  :: "'a \<Rightarrow> 'a \<Rightarrow> prop" (infix "provided" 0)
parse_ast_translation {* [(@{syntax_const "_provided"}, (fn ctxt => fn [p, q] =>
  Ast.Appl [Ast.Constant @{const_syntax "Pure.imp"},
    Ast.Appl [Ast.Constant @{const_syntax "IFOL.Trueprop"}, q],
    Ast.Appl [Ast.Constant @{const_syntax "IFOL.Trueprop"}, p]
  ]))] *}

text_raw {*\DefineSnippet{abbrevmeansequals}{*}
abbreviation (input) means_prefix
   ("let _ func _ \<rightarrow> _ means _" [0,0,0] 10)
where "let lt func def \<rightarrow> dom means cond \<equiv>
  def = the1 (\<lambda>it. lt implies (it is dom & cond(it)))"

abbreviation (input) equals_prefix
   ("let _ func _ \<rightarrow> _ equals _" [0,0,0] 10)
where "let lt func def \<rightarrow> dom equals exp \<equiv>
   def = the1 (\<lambda>it. lt implies (it is dom & it = exp))"
text_raw {*}%EndSnippet*}

abbreviation (input) equals_prefix_nolet
   ("func _ \<rightarrow> _ equals _" [10,10] 10)
where "equals_prefix_nolet(a,b,c) \<equiv> a = the1 (\<lambda>it.((it is b) & (it = c)))"

abbreviation (input) mode_prefix
  ("let _ mode _ \<rightarrow> _ means _" [10,10,10] 10)
where "mode_prefix(lt,def,dom,cond) \<equiv> def = typexp(\<lambda>it. lt implies ((it is dom) & cond(it)))"

(* Here we use the following syntax translation instead of an abbreviation to introduce a
   named lambda.
abbreviation attr_prefix ("let _ attr _ means _" [10,10,10] 10)
where "attr_prefix(lt,X,def,exp) == def = attribute(\<lambda>it. lt(it) implies exp(it))" *)

syntax attr_prefix :: "o \<Rightarrow> s \<Rightarrow> ty \<Rightarrow> o \<Rightarrow> o" ("let _ attr _ is _ means _" [10,10,10,10] 10)
translations "attr_prefix(lt,X,def,exp)" => "def = CONST attribute(\<lambda>X. lt implies exp)"

abbreviation (input) attr_prefix_nolet ("attr _ means _" [10,10] 10)
where "attr_prefix_nolet(def,exp) == def = attribute(\<lambda>it. exp(it))"

abbreviation (input) mode_prefix_nolet ("mode _ \<rightarrow> _ means _" [10,10,10] 10)
where "mode_prefix_nolet(M,b,c) \<equiv> M = typexp(\<lambda>it.((it is b) & c(it)))"

abbreviation (input) cluster_prefix_fun ("let _ cluster _ \<rightarrow> _" [10,10,10] 10)
where "cluster_prefix_fun(lt,fun,attrs) \<equiv> (lt implies fun is attrs)"

abbreviation (input) cluster_prefix_ex ("let _ cluster _ for _" [10,10,10] 10)
where "cluster_prefix_ex(lt,attrs,type) == (lt implies (ex X being type st X is attrs))"

abbreviation (input) cluster_prefix_attrs ("let _ cluster _ \<rightarrow> _ for _" [10,10,10,10] 10)
where "cluster_prefix_attrs(lt,attrs1,attrs2,type) == (lt implies (for X being type st X is attrs1 holds X is attrs2))"

abbreviation (input) cluster_prefix_fun_nolet ("cluster _ \<rightarrow> _" [10,10] 10)
where "cluster_prefix_fun_nolet(fun,attrs) \<equiv> fun is attrs"

abbreviation cluster_prefix_ex_nolet ("cluster _ for _" [10,10] 10)
where "cluster_prefix_ex_nolet(attrs,type) \<equiv> (ex X being type st X is attrs)"

end
