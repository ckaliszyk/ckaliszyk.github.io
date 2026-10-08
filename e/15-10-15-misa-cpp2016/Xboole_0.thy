theory Xboole_0
imports Tarski
begin

(*XBOOLE_0*)

text_raw {*\DefineSnippet{xboolesch1}{*}
theorem xboole_0_sch_1:
  "ex X being set st for x being object holds
      x in X iff x in A & P(x)
provided
   A is set"
text_raw {*}%EndSnippet*}
proof-
text_raw {*\DefineSnippet{xboolesch1prf}{*}
  assume A0:"A is set"
  let ?Q = "\<lambda>x. \<lambda>y. (x=y & P(x))"
  have A1: "for x,y,z being object holds
    ?Q(x, y) & ?Q(x, z) implies y = z" by auto 
  obtain X where
  A2:"X is set & (for x being object holds x in X iff
    (ex y being object st y in A & ?Q(y, x)))"
       using tarski_sch_1[OF A0 A1] by auto
  thus "ex X being set st
    (for x being object holds x in X iff x in A & P(x))"
      by auto
text_raw {*}%EndSnippet*}
qed

text_raw {*\DefineSnippet{defempty}{*}
definition xboole_0_def_1[simp]:
  "let X is set attr X is empty means
    not (ex x being object st x in X)"
text_raw {*}%EndSnippet*}

theorem xboole_0_def_1a[simp]:
  "X is set \<Longrightarrow>
    X is empty iff not (ex x being object st x in X)"
      using xboole_0_def_1 attr_spec by auto

text {*
 \DefineSnippet{defemptythm}{
    @{thm [display] xboole_0_def_1a[no_vars]}
 }%EndSnippet
*}

text_raw {*\DefineSnippet{clusterempty}{*}
theorem xboole_0_cl_1[simp]:
   "cluster empty for set"
text_raw {*}%EndSnippet*}
proof -
   let ?P = "\<lambda>x. False"
   have A0:"(the set) is set" using the_property set_exists by auto
  obtain X where
   A1:"X is set & (for x being object holds x in X iff x in (the set) & ?P(x))" using xboole_0_sch_1[OF A0, of ?P] by blast
   have "not(ex x being object st (x in X))" using A1 by auto
   thus ?thesis using A1 by auto
qed

text_raw {*\DefineSnippet{theemptyset}{*}
definition xboole_0_def_2_prefix ("{}") where
  "func {} \<rightarrow> set equals the empty set"
text_raw {*}%EndSnippet*}

schematic_theorem xboole_0_def_2[simp]:
  shows "?X"
proof (rule equals_property_nolet[OF xboole_0_def_2_prefix_def])
  show "(the empty set) is set" using the_property[of "tys(empty, set)"] xboole_0_cl_1 by auto
qed

definition prefix_cup (infixl "\<union>" 65) where
"let X be set & Y be set
  func X \<union> Y \<rightarrow> set means \<lambda>it. for x being object holds x in it iff x in X or x in Y"

schematic_theorem xboole_0_def_3[simp]:
  assumes "X is set & Y is set" shows "?X"
proof (rule means_property[OF prefix_cup_def assms])
   show "ex it being set st for x being object holds (x in it iff x in X or x in Y)"
    proof -
      have "(union {X,Y}) is set & (for x being object holds (x in union {X,Y} iff x in X or x in Y))"
        proof (intro conjI)
          show "(union {X,Y}) is set" using assms tarski_def_2 tarski_def_4 by auto
          show "for x being object holds (x in union {X,Y} iff x in X or x in Y)"
            proof (intro ballI,rule iffI2)
              fix x
              assume Z1: "x is object"
              show "x in union {X,Y} implies x in X or x in Y"
                proof
                  assume "x in union { X , Y }"
                  then have "ex Z being set st x in Z & Z in {X,Y}" using  assms tarski_def_2 tarski_def_4 using Z1 tarski_def_4 by auto
                  thus "x in X or x in Y" using  assms tarski_def_2 by auto
                qed
              have "X in {X,Y} or Y in {X,Y}" using assms tarski_def_2 by auto
              then   show "(x in X or x in Y) implies x in union {X,Y}" using assms Z1 tarski_def_2 tarski_def_4 by auto
            qed
        qed
     thus ?thesis by auto
  qed
  fix A1 A2
  assume T1:"A1 is set" and
        A1: "(for x being object holds (x in A1 iff x in X or x in Y))" and
        T2: "A2 is set" and
        A2: "(for x being object holds (x in A2 iff x in X or x in Y))"
    {
      fix x
      assume Z1: "x is object"
      have "x in A1 iff (x in X or x in Y)" using Z1 A1 by auto
      then have "x in A1 iff  x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" using tarski_th_2 T1 T2 by auto
qed

theorem cup_commutativity[simp]: "for X,Y being set holds X \<union> Y = Y \<union> X"
proof (intro ballI)
   fix X Y
   assume T0:"X is set" "Y is set"
   have T1: "(X \<union> Y)  is set & (Y \<union> X) is set" using xboole_0_def_3 T0 by simp
   {fix x
    assume T1:"x is object"
    have "x in X\<union>Y iff x in X or x in Y" using xboole_0_def_3 T0 T1 by  auto
    hence "x in X\<union>Y iff x in Y\<union>X" using xboole_0_def_3 T0 T1 by auto
  }
  thus "X \<union> Y = Y \<union> X" using tarski_th_2 T1 by auto
qed

theorem cup_idempotence[simp]: "for X being set holds X \<union> X = X" 
proof (intro ballI)
   fix X
   assume T0:"X is set"
   {
     fix x
     assume T1:"x is object"
     have "x in X\<union>X iff x in X " using xboole_0_def_3 T0 T1 by  auto   
   }
   thus "X \<union> X = X" using tarski_th_2 T0 xboole_0_def_3 by blast
qed

definition prefix_cap (infixl "\<inter>" 70) where
"let X be set & Y be set
  func X \<inter> Y \<rightarrow> set means \<lambda>it. for x being object holds (x in it iff (x in X & x in Y))"

schematic_theorem xboole_0_def_4:
  assumes "X is set & Y is set" shows "?X"
proof (rule means_property[OF prefix_cap_def assms])
  show  "ex Z being set st for x being object holds (x in Z iff (x in X & x in Y))"
    using xboole_0_sch_1 assms by auto
  fix A1 A2
  assume T0:"A1 is set" "A2 is set"
  assume A1: "for x being object holds (x in A1 iff (x in X & x in Y))"
     and A2: "for x being object holds (x in A2 iff (x in X & x in Y))"
  {
      fix x
      assume T1:"x is object"
      have "x in A1 iff (x in X & x in Y)" using A1 T0 T1 by auto
      then have "x in A1 iff x in A2" using A2 T0 T1 by auto
  }
  thus "A1 = A2" using tarski_th_2 T0 by auto
qed

theorem cap_commutativity[simp]: "for X being set, Y being set holds X \<inter> Y = Y \<inter> X"
proof (intro ballI)
   fix X Y
   assume T0:"X is set" "Y is set"
   have T1:"(X \<inter> Y) is set &  (Y \<inter> X) is set" using T0 xboole_0_def_4 by auto
   {fix x
    assume T1:"x is object"
    have "x in X\<inter>Y iff x in X & x in Y" using xboole_0_def_4 T0 T1 by  auto
    hence "x in X\<inter>Y iff x in Y\<inter>X" using xboole_0_def_4 T0 T1 by auto
  }
  thus "X \<inter> Y = Y \<inter> X" using tarski_th_2 T1 by auto
qed

theorem cap_idempotence[simp]: "for X being set holds X \<inter> X = X"
proof (intro ballI)
   fix X
   assume T0:"X is set"
   hence T1: "(X \<inter> X) is set" using xboole_0_def_4 by auto
   {
     fix x
     assume T1:"x is object"
     have "x in X\<inter>X iff x in X " using xboole_0_def_4 T0 T1 by  auto   
   }
   thus "X \<inter> X = X" using tarski_th_2 T0 T1 by auto
qed

definition prefix_min (infixl "\\" 70) where
"let X be set & Y be set
  func X \\ Y \<rightarrow> set means \<lambda>it.
    for x being object holds (x in it iff (x in X & not x in Y))"

schematic_theorem xboole_0_def_5:
  assumes "X is set & Y is set" shows "?X"
proof (rule means_property[OF prefix_min_def assms])
  show  "ex Z being set st for x being object holds (x in Z iff (x in X & not x in Y))"
    using xboole_0_sch_1 assms by auto
  fix A1 A2
  assume T0:"A1 is set" "A2 is set"
  assume A1: "for x being object holds (x in A1 iff (x in X & not x in Y))"
     and A2: "for x being object holds (x in A2 iff (x in X & not x in Y))"
  {
      fix x
      assume T1:"x is object"
      have "x in A1 iff (x in X & not x in Y)" using A1 T0 T1 by auto
      then have "x in A1 iff x in A2" using A2 T0 T1 by auto
  }
  thus "A1 = A2" using tarski_th_2 T0 by auto
qed


definition xboole_0_def_6_prefix (infixl "\\+\\" 65)
where
"let X is set & Y is set
 func X \\+\\ Y \<rightarrow> set equals (X \\ Y) \<union> (Y \\ X)"

schematic_theorem xboole_0_def_6:
   assumes "X is set & Y is set"
   shows "?X"
proof (rule equals_property[OF xboole_0_def_6_prefix_def assms])
  show "((X \\ Y) \<union> (Y \\ X)) is set" using assms xboole_0_def_5 by auto
qed

theorem sccap_commutativity[simp]: "for X, Y being set holds X \\+\\ Y = Y \\+\\ X"
proof (intro ballI)
  fix X Y
  assume T0:"X is set" "Y is set"
  hence "(X \\ Y) is set &  (Y \\ X) is set" using xboole_0_def_5 by auto
  thus  "X \\+\\ Y = Y \\+\\ X" using xboole_0_def_6 T0 cup_commutativity by auto
qed

definition
  prefix_misses :: "s \<Rightarrow> s \<Rightarrow> o" (infixl "misses" 40)
where
  xboole_0_def_7[simp]: "X is set & Y is set \<Longrightarrow> (X misses Y) iff X \<inter> Y = {}"

theorem misses_symmetry[simp]:
  "for X,Y being set holds X misses Y iff Y misses X" 
proof(intro ballI)
  fix X Y
  assume T0:"X is set" "Y is set"
  have "X misses Y iff Y  \<inter> X={}" using T0 cap_commutativity  by auto
  thus "X misses Y iff Y misses X" using T0 by auto
qed

definition
  prefix_xboole_0_def_8 :: "s \<Rightarrow> s \<Rightarrow> o" (infixl "c<" 40)
where
  xboole_0_def_8[simp]: "(X c< Y) iff X c= Y & X<>Y"

theorem xboole_0_def_8_irreflexivity[simp]:
  "for X being set holds not (X c< X)" using  xboole_0_def_8 by auto

theorem xboole_0_def_8_asymmetry[simp]:
  "for X,Y being set st X c< Y holds not (Y c< X)"
proof (intro ballI,intro impI)
  fix X Y
  assume T0:"X is set" "Y is set"
  assume A1:"X c<Y"
  show "not (Y c<X)"
   proof
    assume A2: "Y c< X"
     {
        fix x
        assume T1:"x is object"
        have A3:"x in X implies x in Y" using tarski_def_3 T0 T1 A1 by auto
        have   "x in Y implies x in X" using tarski_def_3 T0 T1 A2 by auto
        hence "x in X iff x in Y" using A3 by auto
     }
    hence "X = Y" using tarski_th_2 T0 by auto
    thus "False" using A1 by auto
   qed
qed

definition
  prefix_xboole_0_def_9 :: "s \<Rightarrow> s \<Rightarrow> o" ("_ , _ are c= comparable"[50,50] 40)
where
  xboole_0_def_9[simp]: "X is set & Y is set \<Longrightarrow> 
       X,Y are c= comparable iff (X c= Y or Y c= X)"

theorem  xboole_0_def_9_symmetry[simp]:
  "for X,Y being set st X,Y are c= comparable holds Y,X are c= comparable" by auto 

theorem xboole_0_def_10: "for X,Y being set holds X = Y iff (X c= Y & Y c= X)"
proof (intro ballI)
  fix X Y
  assume T0: "X is set" "Y is set"
  show "X = Y iff (X c= Y & Y c= X)"
    proof (rule iffI2)
    show "X = Y implies (X c= Y & Y c= X)" by auto
    show "(X c= Y & Y c= X) implies X=Y"
      proof
        assume A1:"X c= Y & Y c= X"
          {
            fix x
            assume T1:"x is object"
            have A2:"x in X implies x in Y" using tarski_def_3 T0 T1 A1 by blast
            have   "x in Y implies x in X" using tarski_def_3 T0 T1 A1 by blast
            hence "x in X iff x in Y" using A2 by auto
          }
        thus "X=Y" using T0 tarski_th_2 by auto
      qed
  qed
qed

abbreviation meets_prefix :: "s \<Rightarrow> s \<Rightarrow> o" ("_ meets _" 40)
  where "X meets Y == not (X misses Y)"



theorem xboole_0_th_1:
  "for X,Y,Z being set,x being object holds x in X \\+\\ Y iff not (x in X iff x in Y)" 
proof(intro ballI)
  fix X Y Z
  assume T0:"X is set" "Y is set" "Z is set" 
  fix x 
  assume T1: "x is object"
  have "x in X \\+\\ Y iff x in X \\ Y or x in Y \\ X"
    using xboole_0_def_6 xboole_0_def_3 xboole_0_def_5 T0 T1 by auto
  thus "x in X \\+\\ Y iff not (x in X iff x in Y)" using xboole_0_def_5 T0 T1 by auto
qed

theorem xboole_0_th_2:
  "for X,Y,Z being set holds
    (for x being object holds (not x in X) iff (x in Y iff x in Z)) implies X = Y \\+\\ Z"
proof (intro ballI)
  fix X Y Z
  assume T1:"X is set" "Y is set" "Z is set"
  show "(for x being object holds (not x in X) iff (x in Y iff x in Z)) implies X = Y \\+\\ Z "
    proof 
      assume A1: "for x being object holds (not x in X) iff (x in Y iff x in Z)"
        { 
          fix x
          assume T2: "x is object"
          have "x in X iff ((x in Y & not x in Z) or (x in Z & not x in Y))" using T2 A1 by auto
          hence "x in X iff (x in Y \\ Z or x in Z \\ Y)" using xboole_0_def_5 using T1 T2 by auto
          hence "x in X iff x in Y \\+\\ Z"
            using xboole_0_def_3 xboole_0_def_5 xboole_0_def_6 T1 T2 by auto
        }
      thus "X = Y \\+\\ Z" using tarski_th_2 T1 xboole_0_def_6 by blast
    qed
qed

theorem xboole_0_cl_2[simp]: 
  "cluster {} \<rightarrow> empty"
proof -
  have "\<exists>x. x is tys(empty,set)" using xboole_0_cl_1 by auto
  hence "(the empty set) is tys(empty,set)" using xboole_0_def_2 the_property by blast 
  thus "{} is empty" using xboole_0_def_2 by auto
qed

theorem xboole_0_cl_3[rule_format,simp]: 
   "let x be object 
    cluster {x} \<rightarrow> non empty"
proof (intro impI)
  assume T0:"x is object"
  have "x in {x}" using tarski_def_1 T0 by auto
  hence "ex z being object st z in {x}" using T0 by auto
  thus "{x} is non empty" using tarski_def_1 T0 xboole_0_def_1 by auto
qed

theorem xboole_0_cl_4[rule_format]: 
  "let x be object & y be object 
   cluster {x,y} \<rightarrow> non empty"
proof(intro impI)
  assume T0:"x is object & y is object"
  have "x in {x,y}" using tarski_def_2 T0 by auto
  hence "ex z being object st z in {x,y}" using T0 by auto
  thus "{x,y} is non empty" using tarski_def_2 T0 xboole_0_def_1 by auto
qed

theorem xboole_0_cl_5:
  "cluster non empty for set"
proof-
  have "(the object) is object" using object_exists the_property by auto
  hence "{the object} is non empty set" using xboole_0_cl_3 tarski_def_1 by auto
  thus ?thesis by auto
qed

theorem xboole_0_cl_6:
  "let D be non empty set & X be set
   cluster D \<union> X \<rightarrow> non empty"
proof (intro impI)
  assume A0: "D is non empty set & X is set"
  obtain x where
    A1: "x is object & x in D" using A0 xboole_0_def_1 by auto
  hence "x in D \<union> X" using xboole_0_def_3 A0 by auto
  thus "(D \<union> X) is non empty" using A0 xboole_0_def_3 xboole_0_def_1 A1 by auto
qed

lemma xboole_0_lm_1:
   "for X being set st X is empty holds X={}"
proof(intro ballI, intro impI)
  fix X
  assume T0:"X is set"
  assume A1: "X is empty"
  hence "not (ex x being object st x in X)" using T0 xboole_0_def_2 by auto
  hence "for x being object holds x in {} iff x in X" using xboole_0_def_2 xboole_0_cl_2 by auto
  thus "X = {}" using tarski_th_2 T0 xboole_0_def_2 by auto
qed

theorem xboole_0_th_3:
  "for X,Y being set holds (X meets Y) iff (ex x being object st x in X & x in Y)"
proof (intro ballI, intro iffI2)
  fix X Y
  assume T0:"X is set" "Y is set"
  hence T1: "(X \<inter> Y) is set" using xboole_0_def_4 by auto
  show "(X meets Y) implies (ex x being object st x in X & x in Y)"
    proof
      assume "X meets Y"
      hence "X \<inter> Y <>{} " using T0 by auto
      hence "(X \<inter> Y) is non empty" using xboole_0_lm_1 T1 by auto
      then obtain x where
         A1:"x is object & x in X\<inter>Y" using xboole_0_def_1 by auto
      have "x is object & x in X & x in Y" using A1 xboole_0_def_4 T0 by auto        
      thus "ex x being object st x in X & x in Y" by auto
    qed
  show "(ex x being object st x in X & x in Y) implies (X meets Y)"
    proof
      assume "ex x being object st x in X & x in Y"
      then obtain x where
      A2:"x is object & x in X & x in Y" by auto
      have "x in X\<inter>Y" using A2 xboole_0_def_4 T0 by auto
      hence "X \<inter> Y <> {}" using xboole_0_cl_2 xboole_0_def_1 T1 A2 by auto
      thus "X meets Y" using T0 by auto
    qed
qed

theorem xboole_0_th_4:
  "for X,Y being set holds (X meets Y) iff (ex x being object st x in X\<inter> Y)"
proof (intro ballI, intro iffI2)
  fix X Y
  assume T0:"X is set" "Y is set"
  hence T1: "(X \<inter> Y) is set" using xboole_0_def_4 by auto
  show "(X meets Y) implies (ex x being object st x in X\<inter> Y)"
    proof
      assume "X meets Y"
      hence "X \<inter> Y <>{} " using T0 by auto
      hence "(X \<inter> Y) is non empty" using xboole_0_lm_1 T1 by auto
      then obtain x where
         A1:"x is object & x in X\<inter>Y" using xboole_0_def_1 by auto
      have "x is object & x in X \<inter> Y" using A1 by auto        
      thus "ex x being object st x in X \<inter> Y" by auto
    qed
  show "(ex x being object st x in X\<inter>Y) implies (X meets Y)"
    proof
      assume "ex x being object st x in X\<inter> Y"
      then obtain x where
      A2:"x is object & x in X \<inter> Y" by auto
      have "X \<inter> Y <> {}" using xboole_0_cl_2 xboole_0_def_1 T1 A2 by auto
      thus "X meets Y" using T0 by auto
    qed
qed


theorem
  "for X,Y being set, x being object st
    X misses Y & x in X \<union> Y holds ((x in X & not x in Y) or (x in Y & not x in X))"
proof (intro ballI, intro impI)
  fix X Y x
  assume T0:"X is set" "Y is set" "x is object"
  assume A1:"X misses Y & x in X \<union> Y"
  hence "x in X or x in Y" using xboole_0_def_3 T0 by auto
  thus "(x in X & not x in Y) or (x in Y & not x in X)" using A1 T0 xboole_0_th_3 by auto
qed

theorem xboole_0_sch_2:
  "X = Y
provided
    (X is set) & (Y is set) &
    (for x being object holds (x in X iff P(x))) &
    (for x being object holds (x in Y iff P(x)))"
proof (elim conjE)
  assume A1: "X is set" "Y is set"
     and A2:"for x being object holds (x in X iff P(x))"
     and A3: "for x being object holds (x in Y iff P(x))"
  have A4:"for x being object holds (x in X implies x in Y)" using A2 A3 by auto
  have "for x being object holds (x in Y implies x in X)" using A2 A3 by auto
  hence "for x being object holds (x in X iff x in Y)" using A4 by auto
  thus "X = Y" using tarski_th_2 A1 by auto
qed

theorem xboole_0_sch_3:
fixes P
shows "for X1,X2 being set holds ((for x being object holds (x in X1 iff P(x))) &
                         (for x being object holds (x in X2 iff P(x))) implies (X1 = X2))"
proof(intro ballI)
   fix X1 X2
   assume A0: "X1 is set" "X2 is set"
   show "(for x being object holds (x in X1 iff P(x))) &
         (for x being object holds (x in X2 iff P(x))) implies (X1 = X2)" 
      proof (intro impI,elim conjE)
        assume A1: "for x being object holds (x in X1 iff P(x))" and
               A2: "for x being object holds (x in X2 iff P(x))"
        have A4: "(
         (X1 is set) & (X2 is set) &
         (for x being object holds (x in X1 iff P(x))) &
         (for x being object holds (x in X2 iff P(x))))" using A0 A1 A2 by auto
        show "X1=X2" using xboole_0_sch_2[OF A4] by iprover
     qed
qed

text_raw {*\DefineSnippet{xboole0th6}{*}
theorem xboole_0_th_6:
  "for X,Y being set st X c< Y holds
     ex x being object st x in Y & not x in X"
text_raw {*}%EndSnippet*}
  using xboole_0_def_8 xboole_0_def_10 tarski_def_3 by auto

theorem xboole_0_th_7:
  "for X being set st X <> {} holds ex x being object st x in X"
    using xboole_0_def_1 xboole_0_lm_1 by auto

text_raw {*\DefineSnippet{xboole0th8}{*}
theorem xboole_0_th_8:
  "for X,Y being set st X c< Y holds
     ex x being object st x in Y & X c= Y\\{x}"
text_raw {*}%EndSnippet*}
proof (intro ballI, intro impI)
  fix X Y
  assume T0:"X is set" "Y is set"
  assume A1:"X c< Y"
  then obtain x where
    T1:"x is object" and A2: "x in Y" and
    A3:" not x in X" using xboole_0_th_6 T0 by blast 
  have T1_1:"{x} is set" using T1 tarski_def_1 by auto
  have "x is object & x in Y & X c= Y\\{x}"
    proof (intro conjI)
       show "x is object" using T1 by simp
       show "x in Y" using A2 by simp
       show "X c= Y\\{x}" unfolding tarski_def_3
         proof (intro ballI,intro impI)         
            fix y
            assume T2:"y is object"
            assume A4:"y in X"
            hence "y <>x" using A3 by auto
            hence A5: "not y in {x}" using tarski_def_1 T1 T2 by auto
            have "X c= Y" using A1 by auto 
            hence "y in Y" using A4 T1 T2 tarski_def_3 by auto
            thus "y in Y\\{x}" using A5 T0 T1_1 T2 xboole_0_def_5 by auto
         qed
    qed
  thus "ex x being object st x in Y & X c= Y\\{x}" by auto    
qed

abbreviation include_antyonym :: "s \<Rightarrow> s \<Rightarrow> o" ("_ c\\= _" 40)
  where "X c\\= Y == not (X c= Y)"

abbreviation in_antonym :: "s \<Rightarrow> s \<Rightarrow> o" ("_ nin _" 40)
  where "X nin Y == not (X in Y)"

end
