(* This Isabelle theory file combines three Mizar articles: TARSKI_0, TARSKI, TARSKI_A *)
theory Tarski
imports Hidden
begin

(* TARSKI_0 *)

text_raw {*\DefineSnippet{tarski0}{*}

--"Set axiom"
axiomatization where tarski_0_1:
  "for x being object holds x is set"

--"Extensionality axiom"
axiomatization where tarski_0_2:
  "for X,Y being set holds
    (for x being object holds x in X iff x in Y) implies X = Y"

--"Axiom of pair"
axiomatization where tarski_0_3:
  "for x,y being object holds ex z being set st
     for a being object holds
       a in z iff a = x or a = y"

--"Axiom of union"
axiomatization where tarski_0_4:
  "for X being set holds
     ex Z being set st
       for x being object holds
         x in Z iff (ex Y being set st x in Y & Y in X)"

--"Axiom of regularity"
axiomatization where tarski_0_5:
  "for x being object,X being set st
     x in X holds (ex Y being set st Y in X &
       not (ex z being object st z in X & z in Y))"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{tarski0sch}{*}
--"Fraenkel's scheme"
axiomatization where tarski_0_sch_1:
  "A is set \<Longrightarrow> (
     ex X being set st for x being object holds
       x in X iff (ex y being object st y in A & P(y, x))
  provided
    for x,y,z being object
       st P(x, y) & P(x, z) holds y = z)"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{setexists}{*}
theorem set_exists[simp]: "ex x being set st True"
text_raw {*}%EndSnippet*}
text_raw {*\DefineSnippet{setexistsprf}{*}
proof -
  have "(the object) is set" using object_exists the_property tarski_0_1 by auto
  thus ?thesis by auto
qed
text_raw {*}%EndSnippet*}

(* TARSKI *)

theorems tarski_th_2 = tarski_0_2

text_raw {*\DefineSnippet{defsing}{*}
definition tarski_def_1 ("{_}") where
   "let y be object
   func {y} \<rightarrow> set means \<lambda>it.
   for x being object holds x in it iff x = y"
text_raw {*}%EndSnippet*}

schematic_theorem tarski_def_1:
  assumes "y is object" shows "?X"
proof (rule means_property[OF tarski_def_1_def assms])
text_raw {*\DefineSnippet{defsingprf}{*}
  show "ex X being set st for x being object
    holds x in X iff x = y"
  proof-
    obtain X where
      A1: "X is set & (for x being object holds
        (x in X iff (x = y or x = y)))"
           using tarski_0_3 assms by blast
    then have "X is set &
      (for x being object holds x in X iff x = y)" by auto
    thus ?thesis by auto
  qed

  fix X1 X2
  assume A1: "X1 is set" and A2: "X2 is set" and
         A3: "for x being object holds x in X1 iff x = y" and
        A4: "for x being object holds x in X2 iff x = y"
  {
    fix x
    assume Z1: "x is object"
    have "x in X1 iff x = y" using Z1 A1 A3 by auto
    hence "x in X1 iff x in X2" using Z1 A2 A4 by auto
  }
  thus "X1 = X2" using tarski_th_2 A1 A2 by blast
text_raw {*}%EndSnippet*}
qed

lemmas tarski_def_1a = tarski_def_1[THEN conjunct1,THEN conjunct1,simplified,rule_format]
lemmas tarski_def_1b = tarski_def_1[THEN conjunct1,THEN conjunct2,simplified,rule_format]
lemmas tarski_def_1c = tarski_def_1[THEN conjunct2,simplified,rule_format,unfolded atomize_conjL[symmetric],folded Ball_def]

text {*
 \DefineSnippet{defsingthms}{
    @{thm [display] tarski_def_1a[no_vars]}
    @{thm [display] tarski_def_1b[no_vars]}
    @{thm [display] tarski_def_1c[no_vars]}
 }%EndSnippet
*}

definition setpair ("{ _ , _ }") where
"let y be object & z be object
  func {y, z} \<rightarrow> set means \<lambda>it. for x being object holds x in it iff (x = y or x = z)"

schematic_theorem tarski_def_2:
  assumes "y is object & z is object" shows "?X"
proof (rule means_property[OF setpair_def assms])
show  "ex it being set st for x being  object holds (x in it iff x = y or x = z)"
proof -
  obtain X where
  A1: "X is set & (for x being object holds (x in X iff (x = y or x = z)))" using tarski_0_3 assms by blast
  thus ?thesis by auto
qed
fix IT1 IT2
assume A: "IT1 is set" "for x being object holds (x in IT1 iff x = y or x = z)"
          "IT2 is set" "for x being object holds (x in IT2 iff x = y or x = z)"
{
     fix x
     assume Z1: "x is object"
     have "x in IT1 iff x=y or x = z" using Z1 A(2) by auto
     hence "x in IT1 iff x in IT2" using Z1 A(4) by auto
 }
thus "IT1 = IT2" using tarski_th_2 A by blast
qed

text_raw {*\DefineSnippet{tarskidef2commutativity}{*}
theorem tarski_def_2_commutativity[simp]:
  "for x,y being object holds {x,y} = {y,x}"
text_raw {*}%EndSnippet*}
proof(intro ballI)
  fix x y
  assume T0:"x is object" "y is object"
  have A1: "{x,y} is set & {y,x} is set" using tarski_def_2 T0 by auto
  {fix z
   assume T1: "z is object"
   have "z in {x,y} iff z = x or z = y" using T0 T1 tarski_def_2 by auto
   hence "z in {x,y} iff z in {y,x}" using T0 T1 tarski_def_2 by auto
  }
  thus "{x,y}={y,x}" using tarski_th_2 A1 by auto
qed

definition tarski_def_3_prefix:: "s \<Rightarrow> s \<Rightarrow> o" (infixl "c=" 50)
where tarski_def_3[simp]: "X c= Y iff (for x being object holds x in X implies x in Y)"

text_raw {*\DefineSnippet{defunion}{*}
definition tarski_def_4 ("union _" [90] 90) where
   "let X be set
   func union X \<rightarrow> set means \<lambda>it.
   for x being object holds
   x in it iff (ex Y being set st x in Y & Y in X)"
text_raw {*}%EndSnippet*}

schematic_theorem tarski_def_4:
  assumes "X is set" shows "?X"
proof (rule means_property[OF tarski_def_4_def assms])
show "ex IT being set st for x being object holds x in IT iff (ex Y being set st x in Y & Y in X)" using tarski_0_4 assms by blast

 fix IT1 IT2
assume T0: "IT1 is set" "IT2 is set"
  assume A1: "for x being object holds (x in IT1 iff (ex Y being set st (x in Y & Y in X)))" and
         A2: " for x being object holds (x in IT2 iff (ex Y being set st (x in Y & Y in X)))"
 {
     fix x
     assume T1:"x is object"
     have "x in IT1 iff (ex Y being set st (x in Y & Y in X))" using A1 T0 T1 by simp
     hence "x in IT1 iff x in IT2" using A2 T0 T1 by simp
 }
 thus "IT1 = IT2" using tarski_th_2 T0 by auto
qed

theorems tarski_th_3 = tarski_0_5

text_raw {*\DefineSnippet{prefixinassymetry}{*}
theorem prefix_in_asymmetry[simp]:
  "for x,X being set holds not (x in X & X in x)"
text_raw {*}%EndSnippet*}
proof (intro ballI notI)
  fix a b
  assume T0:"a is set" "b is set"
  assume A1:"a in b & b in a"
  have "a is object" using T0 by simp
  let ?X = "{a,b}"
  have T1: "?X is set" using T0 tarski_def_2 by auto
  have "a in ?X & b in {a,b}" using A1 T0 tarski_def_2 by auto
  hence "ex Y being set st Y in ?X & not(ex z being object st z in ?X & z in Y)" using tarski_0_5 T0 T1 by auto
  then obtain Y where
  A4: "Y is set & Y in ?X & not(ex z being object st z in ?X & z in Y)"
    using tarski_0_5 T0 T1 by auto
  have "Y=a or Y=b" using A4 T0 tarski_def_2 by auto
  then show False using A1 A4 T0 tarski_def_2 by auto
qed

theorems tarski_sch_1 = tarski_0_sch_1

text_raw {*\DefineSnippet{defpair}{*}
definition tarski_def_5 ("[_ , _]") where 
   "let x be object & y be object
   func [x,y] \<rightarrow> object equals
   {{x, y}, {x}}"
text_raw {*}%EndSnippet*}

schematic_theorem tarski_def_5:
  assumes "x is object & y is object" shows "?X"
proof (rule equals_property[OF tarski_def_5_def assms])
  show "{{x, y}, {x}} is object" using assms tarski_def_1 tarski_def_2 by auto
qed

definition
  are_equipotent_prefix :: "s \<Rightarrow> s \<Rightarrow> o" ("_,_ areequipotent" [100,100])
where
  tarski_def_6: "X is set & Y is set \<Longrightarrow>
    X, Y areequipotent iff
    (ex Z being set st
     (for x being object st x in X ex y being object st y in Y & [x,y] in Z) &
     (for y being object st y in Y ex x being object st x in X & [x,y] in Z) &
     (for x being object,y being object,z being object,u being object st [x,y] in Z & [z,u] in Z holds (x = z iff y = u)))"

(*TARSKI_A*)
text_raw {*\DefineSnippet{tarskiA}{*}
--"Tarski's axiom"
axiomatization where tarski_a_th_1:
 "for N being set holds ex M being set st N in M &
  (for X,Y being set holds X in M & Y c= X implies Y in M) &
  (for X being object st X in M ex Z being set st Z in M & 
        (for Y being object st Y c= X holds Y in Z)) &
  (for X being object holds X c= M implies 
        X,M areequipotent or X in M)"

text_raw {*}%EndSnippet*}
end

