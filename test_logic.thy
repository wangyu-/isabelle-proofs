theory test_logic
  imports Main
begin
 declare [[simp_trace]]
declare [[simp_trace_depth_limit=10]]

lemma "P\<and>Q\<Longrightarrow>P"
proof -
  assume "P\<and>Q"
  thus P by (rule conjunct1)
qed
lemma tt:"P\<Longrightarrow>P\<or>Q"
proof -
  assume P
  thus "P\<or>Q" by (rule disjI1)
qed
lemma "P\<Longrightarrow>P\<or>Q"
  apply (insert tt)
  apply(rule disjI1)
  apply assumption
  done   
lemma " \<not>P\<Longrightarrow>P\<longrightarrow>Q"
proof -
  assume "\<not>P"
  show "P\<longrightarrow>Q"
  proof (rule impI)
    assume  "P"
    from `\<not>P` `P`  show "Q" by (rule notE)
  qed
qed
thm disj_not1
  
lemma "A\<Longrightarrow>(A\<Longrightarrow>B)\<Longrightarrow>B"
proof -
  assume 1:"A"
  assume 2:"A\<Longrightarrow>B"
  from 1 2 show "B" by simp
qed
  
lemma "A\<longrightarrow>(A\<longrightarrow>B)\<longrightarrow>B" by simp
  
lemma "A\<Longrightarrow>A\<longrightarrow>B\<Longrightarrow>B" by simp
    
lemma wy111 :"(P=Q) \<Longrightarrow> (~ P) \<Longrightarrow>~ Q"
apply auto
done

lemma "\<not> (P\<longrightarrow>Q) \<Longrightarrow>P"
proof -
  assume "\<not> (P\<longrightarrow>Q)"
(*    have "(\<not>P\<or>Q) = (P\<longrightarrow>Q )" by (rule disj_not1) *)
  have "(\<not>P\<or>Q) = (P\<longrightarrow>Q )" by (rule disj_not1)
    then have "(P\<longrightarrow>Q) =(\<not>P\<or>Q) " by (rule sym)
    then have "(\<not>(P\<longrightarrow>Q)) = (\<not>(\<not>P\<or>Q)) " by (rule arg_cong)
    then have "(\<not>(P\<longrightarrow>Q)) \<longrightarrow> (\<not>(\<not>P\<or>Q)) " by rule
    from `(\<not>(P\<longrightarrow>Q))  \<longrightarrow> (\<not>(\<not>P\<or>Q))`  `(\<not>(P\<longrightarrow>Q))`  have  "\<not> (\<not>P\<or>Q)" by (rule mp)
    from this have "((~~P)\<and>\<not>Q)" by (rule Meson.not_disjD)
    from this have "(\<not> \<not>P)" by (rule conjunct1)
    from this show "P" by (rule notnotD)
  qed
    
lemma "\<not> (P\<longrightarrow>Q) \<Longrightarrow>P"
proof -
  assume "\<not> (P\<longrightarrow>Q)"
(*    have "(\<not>P\<or>Q) = (P\<longrightarrow>Q )" by (rule disj_not1) *)
  have "(\<not>P\<or>Q) = (P\<longrightarrow>Q )" by (rule disj_not1)
    then have "(P\<longrightarrow>Q) =(\<not>P\<or>Q) " by (rule sym)
    then have "(\<not>(P\<longrightarrow>Q)) = (\<not>(\<not>P\<or>Q)) " by (rule arg_cong)
    from `(\<not>(P\<longrightarrow>Q)) = (\<not>(\<not>P\<or>Q))` `(\<not>(P\<longrightarrow>Q))`  have  "\<not> (\<not>P\<or>Q)" by (rule iffD1)
    from this have "((~~P)\<and>\<not>Q)" by (rule Meson.not_disjD)
    from this have "(\<not> \<not>P)" by (rule conjunct1)
    from this show "P" by (rule notnotD)
  qed
    
lemma "\<not> (P\<longrightarrow>Q) \<Longrightarrow>P"
proof -
  assume "\<not> (P\<longrightarrow>Q)"
  have "(\<not>P\<or>Q) = (P\<longrightarrow>Q )" by (rule disj_not1) (*<-> is same with =*)
  then have "(P\<longrightarrow>Q) =(\<not>P\<or>Q) " by (rule sym) 
  from   `(P\<longrightarrow>Q) =(\<not>P\<or>Q) ` `\<not> (P\<longrightarrow>Q)`  have  "\<not> (\<not>P\<or>Q)" by (rule subst)
  from this have "((~~P)\<and>\<not>Q)" by (rule Meson.not_disjD)
    from this have "(\<not> \<not>P)" by (rule conjunct1)
    from this show "P" by (rule notnotD)
qed
lemma "\<not> (P\<longrightarrow>Q) \<Longrightarrow>P"
proof -
  assume "\<not> (P\<longrightarrow>Q)"
  have "(\<not>P\<or>Q) \<longleftrightarrow>(P\<longrightarrow>Q )" by (rule disj_not1)
  then have "(P\<longrightarrow>Q) =(\<not>P\<or>Q) " by (rule sym) 
  from   `(P\<longrightarrow>Q) =(\<not>P\<or>Q) ` `\<not> (P\<longrightarrow>Q)`  have  "\<not> (\<not>P\<or>Q)" by (rule subst)
  from this have "((~~P)\<and>\<not>Q)" by (rule Meson.not_disjD)
    from this have "(\<not> \<not>P)" by (rule conjunct1)
    from this show "P" by (rule notnotD)
  qed

    
    
lemma "(\<And>x. P x ) \<Longrightarrow>(\<forall> x. P x )" by auto
  
lemma " (\<forall> x. P x ) \<Longrightarrow> (\<And>x. P x ) " by auto

lemma " (A \<and>C\<Longrightarrow>B) \<Longrightarrow> (B\<Longrightarrow>A\<and>C) \<Longrightarrow> ((A\<and>C)\<equiv>B)" by linarith

lemma " ((A \<Longrightarrow>C)\<Longrightarrow>(B\<Longrightarrow>D)) \<Longrightarrow> ((B\<Longrightarrow>D)\<Longrightarrow>(A\<Longrightarrow>C)) \<Longrightarrow> ((A\<Longrightarrow>C) \<equiv>(B\<Longrightarrow>D))" sorry
    
lemma " (P\<Longrightarrow>False)   \<Longrightarrow> (( (P\<Longrightarrow>False) \<Longrightarrow>False ) \<Longrightarrow>False ) " by auto
    
lemma "(( (P\<Longrightarrow>False) \<Longrightarrow>False ) \<Longrightarrow>False ) \<Longrightarrow> (P\<Longrightarrow>False) " by auto
    
lemma " (( (P\<Longrightarrow>False) \<Longrightarrow>False ) \<Longrightarrow>False ) \<equiv> (P\<Longrightarrow>False)" sorry
      
lemma "  P   \<equiv> ( (P\<Longrightarrow>False) \<Longrightarrow>False ) " oops

lemma " ( P\<Longrightarrow>False)  ( ( (P\<Longrightarrow>False) \<Longrightarrow>False ) \<Longrightarrow>False ) " sorry
  
lemma " ( (\<And>x. P x \<Longrightarrow>False) \<Longrightarrow>False ) \<Longrightarrow> (\<exists> x. P x )" by auto 
    
lemma "(\<exists> x. P x)  \<Longrightarrow> ( (\<And>x. P x \<Longrightarrow>False) \<Longrightarrow>False )" by auto
    
lemma "(true (\<exists> x. P x)) \<equiv> ( (\<And>x. P x \<Longrightarrow>False) \<Longrightarrow>False )" by auto
    
lemma " ( (A\<Longrightarrow>False) \<Longrightarrow>B ) \<Longrightarrow>A \<or> B" by auto 
    
lemma "A \<or> B \<Longrightarrow> ( (A\<Longrightarrow>False) \<Longrightarrow>B )  " by auto
    
lemma " (A  \<Longrightarrow> B ) \<Longrightarrow> (B\<Longrightarrow>A) \<Longrightarrow> A\<equiv>B  " by auto
  
lemma "    \<lbrakk> A \<or> B \<rbrakk> \<equiv> ( (A\<Longrightarrow>False) \<Longrightarrow>B ) " by auto    
    
lemma "(true (A \<or> B) ) \<equiv> ( (A\<Longrightarrow>False) \<Longrightarrow>B )  " by auto    
    
    
lemma "A\<longrightarrow>B\<longrightarrow>C \<Longrightarrow> (A\<Longrightarrow>B\<Longrightarrow>C ) " by auto
    
lemma "(A\<Longrightarrow>B\<Longrightarrow>C) \<Longrightarrow> A\<longrightarrow>B\<longrightarrow>C " by auto
    
lemma " ( ( A\<Longrightarrow>B\<Longrightarrow>False ) \<Longrightarrow>False )  \<Longrightarrow> A\<and>B " by auto

lemma "A\<and>B \<Longrightarrow> ( ( A\<Longrightarrow>B\<Longrightarrow>False ) \<Longrightarrow>False )" by auto
    
lemma " ( A \<Longrightarrow>False )  \<Longrightarrow> \<not>A" by auto

lemma " ( (A\<Longrightarrow>False) \<Longrightarrow>False )  \<Longrightarrow> A" by auto
 
    
 

lemma wy222:"(! x. P (x))\<Longrightarrow> (? x. P x)"  by simp
  
lemma "(! x y. A (x, y) )\<Longrightarrow> ? y. ! x. A(x,y)"
proof -
  assume "! x y. A (x, y)"
  then have "! y x . A( x,y)" by blast
  then have "! y .! x . A(x,y)" by blast
  then show "? y. ! x. A(x,y)" by blast
qed
  
lemma "(! x y. A (x, y) )\<Longrightarrow> ! y. ! x. A(x,y)"
proof -
  assume 1:  "! x y. A (x, y)"
  show "! y. ! x. A(x,y)"
  proof 
    fix y
    show "! x. A(x,y)"
    proof
      fix x
      from 1 have "! y. A(x,y)" by rule
      then show "A(x,y)" by rule
    qed
  qed
    qed

lemma "(? x. !y. A (x, y) )\<Longrightarrow> ! y. ? x. A(x,y)" 
proof -
  assume 1:"(? x. !y. A (x, y) )"
  then obtain x where "!y. A (x, y)" by rule
  show "! y. ? x. A(x,y)"
  proof
    fix y
    show "? x . A(x,y)" 
    proof 
      have "!y. A (x, y)" by fact
      then show "A(x,y)" by rule 
    qed 
   qed
 qed
   
lemma "(? x. !y. A (x, y) )\<Longrightarrow> ! y. ? x. A(x,y)" 
proof -
  assume 1:"(? x. !y. A (x, y) )"
  then obtain x where "!y. A (x, y)" by rule
  have 2:"!y. A (x, y)" by fact
  show "! y. ? x . A(x,y)"
  proof
    fix y
    from 2 have "A(x,y)"  by rule
    then show "? x . A(x,y)" by rule
  qed
qed
   
   
lemma "(? x. ? y. A(x, y) ) = (? y. ? x. A(x,y))"
proof
  assume "(? x. ? y. A(x, y) )"
  then obtain x where "? y. A (x, y)" by rule
  then obtain y where "A(x,y)" by rule
  then have "? x . A(x,y)" by rule
  then show "? y. ? x . A(x,y)" by rule
next
  assume "(? y. ? x. A(x, y) )"
  then obtain y where "? x. A (x, y)" by rule
  then obtain x where "A(x,y)" by rule
  then have "? y . A(x,y)" by rule
  then show "? x. ? y . A(x,y)" by rule
qed

  
lemma ex_or:"(? x . A x \<or> B x )= ((? x. A x) \<or> (? x . B x))"
proof 
  assume "(? x . A x \<or> B x )"
  then obtain x where 1: "A x \<or> B x" by rule
  then show "(? x. A x) \<or> (? x . B x)"
  proof 
    assume "A x"
    then have "? x. A x" by rule
    then show "(? x. A x) \<or> (? x . B x)" by rule
  next
    assume "B x"
    then have "? x. B x" by rule
    then show "(? x. A x) \<or> (? x . B x)" by rule
  qed
next
  assume "(? x. A x) \<or> (? x . B x)"
  then show "(? x . A x \<or> B x )"
  proof
    assume "(? x. A x)"
    then obtain x where " A x" by rule
    then have "( A x \<or> B x )" by rule
    then show "(? x . A x \<or> B x )" by rule
  next
    assume "(? x. B x)"
    then show "(? x . A x \<or> B x )" by auto
  qed
qed

lemma "(! x . A x \<and> B x )= ((! x. A x) \<and> (! x . B x))"
proof
  assume 1:"(! x . A x \<and> B x )"
  
    have 3:"! x .A x " 
    proof
      fix x
      from 1 have 2: "(A x \<and> B x)" by rule
      then have "A x"  by rule
      show "A x" by fact
    qed
    from 1 have  4: "! x. B x" by auto
    from 3 4 show    "(! x. A x) \<and> (! x . B x)" by rule
  next 
    assume "(! x. A x) \<and> (! x . B x)"
    then show "(! x . A x \<and> B x )" by auto
qed
      
      
lemma "(! x . A x \<and> B x )= ((! x. A x) \<and> (! x . B x))"
proof
  assume 1:"(! x . A x \<and> B x )"
  show    "(! x. A x) \<and> (! x . B x)"
    proof -
    have 3:"! x .A x " 
    proof
      fix x
      from 1 have 2: "(A x \<and> B x)" by rule
      then have "A x"  by rule
      show "A x" by fact
    qed
    from 1 have  4: "! x. B x" by auto
    from 3 4 show    "(! x. A x) \<and> (! x . B x)" by auto
 next
    oops

    
lemma wy333:"P \<and> ~ P \<Longrightarrow>False"  
  apply (auto)
done
    
lemma "(~ (? x. A x)) = (! x . ~(A x))"
proof
  assume 1:"~ (? x. A x)"
  show "(! x . ~(A x))"
  proof
    fix x
    show " ~ (A x)"
    proof  
      assume "A x"
      then have 2:" (? x. A x)" by rule
      from 1  2 show "False" by rule
    qed
  qed
next
  assume 1:"(! x . ~(A x))"
  show "~ (? x. A x)"
  proof
    assume "(? x. A x)"
    then obtain x where 2:"(A x)" by rule
    from 1 have 3:"~(A x)" by rule
    (*from 2 3 show  "False" by rule    ----doenst work*)
    from 3 2 show  "False" by rule
  qed
qed
lemma "(~ (! x. A x)) = (? x . ~(A x))"
proof -
  have "(~ (? x. A x)) = (! x . ~(A x))" by auto
  then have "(~(~ (? x. A x))) = (~(! x . ~(A x)))" by simp
  then have "(? x. A x) = (~(! x . ~(A x)))" by simp
  then have "(? x. (~ (A x)) ) = (~(! x . (A x)))" by simp
  then show "(~ (! x. A x)) = (? x . ~(A x))" by rule
qed

(* lemma "(! x . A \<or> B(x)) =A \<or>(! x. B x)"
proof  
  assume 1: "(! x . A \<or> B(x))"
  fix x
  from 1  have "A \<or>( B x)" by rule
  then have "A \<or>(! x. B x)"
  proof
    assume "A"
    have "A" by fact
    then show "A \<or>(! x. B x)" by rule
  next
    assume 2:"( B x)"
    then have "(! x . B x)" by auto
    then show "A \<or>(! x. B x)" by rule
  qed
next *)
  
lemma "(! x . A \<or> B(x)) = (A \<or>(! x. B x))"
proof  
  assume 1: "(! x . A \<or> B(x))"
  have "~A\<or>A" by rule
  then show "A \<or>(! x. B x)"
  proof
    assume 2:"~A"
    have "! x .B(x)" 
    proof
      fix x
      from 1 have 3:"A\<or>B(x)" by rule
      from  2 3 show "B(x)" by simp
    qed
    then show "A \<or>(! x. B x)" by rule
  next
    assume 2:"A"
    have "A" by fact
    then show "A \<or>(! x. B x)" by rule
  qed
next
  assume 0:"(A \<or>(! x. B x))"
  have "~A\<or>A" by rule
  then show "(! x . A \<or> B(x))"
  proof 
    assume A
    then show "(! x . A \<or> B(x))" by simp
  next
    assume 1: "~A"
    from 0 1 have 2:"(! x. B x)" by simp
    show "(! x . A \<or> B(x))"
    proof
      fix x
      from 2 have "B( x)" by rule
      then show "A \<or> B(x)" by rule
    qed
  qed
qed
lemma "(? x . A \<and> (B x)) =(A \<and> (? x . B x))"
proof 
  assume "(? x . A \<and> (B x)) "
  then obtain x where 1: "A \<and> B x" by rule
  then have "B x" by rule
  then have 0:"? x . B x " by rule
  from 1  have "A" by rule
  from `A` 0 show "(A \<and> (? x . B x))" by rule
next
  assume 1: "(A \<and> (? x . B x))"
  then have A by rule
  from 1 have "(? x .(B x) )" by rule
  then obtain x where "B x" by rule
  from `A` `B x` have "A \<and> B(x)"  by rule
  then show "? x . A \<and> (B x)" by rule
qed
lemma temp:"(P\<longrightarrow>Q) = (~ P \<or>Q) " by simp
lemma temp2 :" (~ P \<or>Q) =(P\<longrightarrow>Q)" by simp
lemma temp3 :" (~ P \<or>Q) =(P\<longrightarrow>Q)" by simp

find_theorems "(~ ?P \<or>?Q) =(?P\<longrightarrow>?Q)"

thm temp
  thm temp2
lemma wy444:"(? x . A(x) \<longrightarrow>B(x)  ) =(  (! x .A (x) ) \<longrightarrow> (? x .B(x)) )"
proof -
  have 1:"(? x . A(x) \<longrightarrow>B(x)  ) = (? x.  ~ A x \<or> B x)"  by simp
  have 2:" (? x.  ~ A x \<or> B x) = ( (? x . ~ A x) \<or> (? x . B x) ) " by auto
  from 1  2 have 3:"(? x . A(x) \<longrightarrow>B(x)  ) =  ( (? x . ~ A x) \<or> (? x . B x) ) " by (simp)
  from 3 have 4: "(? x . A(x) \<longrightarrow>B(x)  ) =  ( ~(! x . A x) \<or> (? x . B x) ) "   by simp
  have 5:"( (~(! x . A x)) \<or> (? x . B x) ) = ( (! x .A (x) ) \<longrightarrow> (? x .B(x)) ) " by (rule temp2)
  from 4 5 show "(? x . A(x) \<longrightarrow>B(x)  ) = ( (! x .A (x) ) \<longrightarrow> (? x .B(x)) )" by simp
qed
print_claset
print_simpset
thm wy444
  
lemma "( (! x .A x ) \<longrightarrow>B ) = (? x . (A x \<longrightarrow>B))"
proof -
  have "( (! x .A x ) \<longrightarrow>B )  = ( ~(! x .A x ) \<or> B) " by auto
  then have "( (! x .A x ) \<longrightarrow>B ) = ( (? x . ~A x ) \<or> B)" by auto
  then have "( (! x .A x ) \<longrightarrow>B ) = ( (? x . (~A x)  \<or> B) )" by auto
  then show "( (! x .A x ) \<longrightarrow>B ) = (? x . (A x \<longrightarrow>B))" by auto
qed

lemma "( (? x .A x ) \<longrightarrow>B ) = (! x . (A x \<longrightarrow>B))" by auto
    
lemma "((? x .A x ) \<longrightarrow> (! x. B x) ) \<Longrightarrow> ! x .(A (x) \<longrightarrow>B(x) )" 
proof -
  assume "(? x .A x ) \<longrightarrow> (! x. B x)"
  then have  "(~(? x .A x )) \<or> (! x. B x)" by blast
  then show " ! x .(A (x) \<longrightarrow>B(x) ) "
  proof 
    assume "(~(? x .A x ))"
    then have 1:"! x . ~ (A x)"  by simp
    then show "! x .(A (x) \<longrightarrow>B(x) ) " by auto
  next 
    assume  "(! x. B x)"
    then show "! x .(A (x) \<longrightarrow>B(x) ) " by auto
  qed
qed
  
lemma "((? x .A x ) \<longrightarrow> (! x. B x) ) \<Longrightarrow> ! x .(A (x) \<longrightarrow>B(x) )" 
proof -
  assume "(? x .A x ) \<longrightarrow> (! x. B x)"
  then have  "(~(? x .A x )) \<or> (! x. B x)" by blast
  then show " ! x .(A (x) \<longrightarrow>B(x) ) "
  proof 
    assume "(~(? x .A x ))"
    then have 1:"! x . ~ (A x)"  by simp
    show "! x .(A (x) \<longrightarrow>B(x) ) " 
    proof
      fix x
      from 1 have "~(A x)" by rule
      then have 2: "~(A x) \<or> B x" by rule
      then show "(A x) \<longrightarrow> (B x)" by auto   
    qed
  next 
    assume  3:"(! x. B x)"
    show "! x .(A (x) \<longrightarrow>B(x) )"
    proof
      fix x
      from 3 have "B x" by rule
      then show "(A x) \<longrightarrow>(B x)" by rule
  qed
qed
qed


  
lemma drinker:"\<exists>x.( drunk x \<longrightarrow> (\<forall>x. drunk x) )"
proof -
  have "(\<exists> x.( drunk x \<longrightarrow> (\<forall>x. drunk x) ) ) = (\<exists> x.( ~ (drunk x) \<or> (\<forall>x. drunk x) ) )" by auto
  have "(\<exists> x.( ~ (drunk x) \<or> (\<forall>x. drunk x) ) ) =(\<exists> x.( ~ (drunk x)) \<or>(\<exists> x. (\<forall>x. drunk x) ) ) " by auto 
  have "(\<exists> x. (\<forall>x. drunk x)) = ( \<forall>x. drunk x) " by auto
  have "(\<exists> x.( drunk x \<longrightarrow> (\<forall>x. drunk x) ) ) = (\<exists> x.( ~ (drunk x)))\<or> ( \<forall>x. drunk x)  " by auto
  have "(\<exists> x.( drunk x \<longrightarrow> (\<forall>x. drunk x) ) ) = (\<exists> x.( ~ (drunk x)))\<or> ~( ? x.~ drunk x)  " by auto
  then have "(\<exists> x.( drunk x \<longrightarrow> (\<forall>x. drunk x) ) ) =True" by auto
  then show "(\<exists> x.( drunk x \<longrightarrow> (\<forall>x. drunk x) ) )" by simp
qed
  
lemma pornp: "P \<or> ~P" by blast 
    
    
theorem rich_grandfather: "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow> 
  \<exists>x. rich x \<and> rich (father (father x))"
proof -
  assume 1:"\<forall>x. \<not> rich x \<longrightarrow> rich (father x)"
  then have 1:"\<forall>x. rich x \<or> rich (father x)" by (blast)
  have "(\<exists>x. rich x \<and> ~rich(father x) )  \<or> ~(\<exists>x. rich x \<and> ~rich(father x) )  " by (rule pornp)
  then show "\<exists>x. rich x \<and> rich (father (father x))"
  proof 
    assume "(\<exists>x. rich x \<and> ~rich(father x) )"
    then obtain x where 3:"rich x \<and> ~rich(father x) " by rule
    then have 2:" ~rich(father x)" by rule
    from 1 2 have 4:"rich (father(father x))" by blast
    from 3 have 5:"rich x" by rule
    from 4 5 have "rich x \<and> rich (father (father x))" by  simp
    then show "\<exists>x. rich x \<and> rich (father (father x))" by rule
  next
    assume "~(\<exists>x. rich x \<and> ~rich(father x) )"
    then have 6:"! x. (rich x) \<longrightarrow>rich(father x)" by simp
    have 10:"(\<exists>x. rich x)" 
    proof  (rule ccontr)  (* doenst work without this (rule ccontr) *)
      assume 8:"~ (\<exists>x. rich x)"
      then have "! x. (~ rich x)" by simp
      then obtain x where 7: "~ (rich x)" by rule
      from 7 1 have "rich (father x)" by blast
      then have 9:"(\<exists>x. rich x)" by rule
      from 8 9 show "False" by simp
    qed
    from 10 obtain x where 11:"rich x" by rule
    from 6 this have "rich(father x)" by simp
    from 6 this have "rich(father(father x) )" by simp
    from 11 this have "(rich x) \<and> rich(father(father x)) " by rule
    then show "\<exists>x. rich x \<and> rich (father (father x))" by rule
  qed
qed
  
 theorem rich_grandfather_again: "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow> 
  \<exists>x. rich x \<and> rich (father (father x))"
proof -
  assume 1:"\<forall>x. \<not> rich x \<longrightarrow> rich (father x)"
  then have 1:"\<forall>x. rich x \<or> rich (father x)" by (blast)
  have "(\<exists>x. rich x \<and> ~rich(father x) )  \<or> ~(\<exists>x. rich x \<and> ~rich(father x) )  " by (rule pornp)
  then show "\<exists>x. rich x \<and> rich (father (father x))"
  proof 
    assume "(\<exists>x. rich x \<and> ~rich(father x) )"
    then obtain x where 3:"rich x \<and> ~rich(father x) " by rule
    then have 2:" ~rich(father x)" by rule
    from 1 2 have 4:"rich (father(father x))" by blast
    from 3 have 5:"rich x" by rule
    from 4 5 have "rich x \<and> rich (father (father x))" by  simp
    then show "\<exists>x. rich x \<and> rich (father (father x))" by rule
  next
    assume "~(\<exists>x. rich x \<and> ~rich(father x) )"
    then have 6:"! x. (rich x) \<longrightarrow>rich(father x)" by simp
    have 10:"~~(\<exists>x. rich x)"  (* changed to not form *)
    proof 
      assume 8:"~ (\<exists>x. rich x)"
      then have "! x. (~ rich x)" by simp
      then obtain x where 7: "~ (rich x)" by rule
      from 7 1 have "rich (father x)" by blast
      then have 9:"(\<exists>x. rich x)" by rule
      from 8 9 show "False" by simp
    qed
    from 10 have "(\<exists>x. rich x)" by simp
    then obtain x where 11:"rich x" by rule
    from 6 this have "rich(father x)" by simp
    from 6 this have "rich(father(father x) )" by simp
    from 11 this have "(rich x) \<and> rich(father(father x)) " by rule
    then show "\<exists>x. rich x \<and> rich (father (father x))" by rule
  qed
qed       
lemma fake111:"! x y. ( x=(y::nat)) \<Longrightarrow> ! x y .~(x=y)" by auto

lemma " (x= (y::nat)) \<Longrightarrow> (p=(q::nat))" oops
    
(*
lemma fake222: "( x=(y::nat))" sorry
thm fake222
  
lemma fake333: "(1::nat) = 2" by (rule fake222)
lemma fake444: "~( x=(y::nat))"  
  proof -
    have 1:"~((1::nat) =2)" by auto
    have 2:"(1::nat) = 2" by (rule fake333)
    from 1 2 have "False" by auto
    then show  "~( x=(y::nat))" by auto
  qed 
*)

(* play with set notation *)
lemma "{1} : {{1}}" by auto



lemma " (~( P=Q) )  = ( P = (~ Q) )" by auto
lemma "! P Q. (~( P=Q) )  = ( P = (~ Q) )" by auto
lemma "(! P Q. (~( P=Q) ) ) = (! P Q . ( P = (~ Q) ))" by auto
lemma "(~(! P Q. (( P=Q) ) )) = (! P Q . ( P = (~ Q) ))" oops
    
lemma " (~( P x =Q x) )  = ( P x = (~ Q x ))" by auto
lemma " ! x . (~( P x =Q x) )  = ( P x = (~ Q x ))" by auto  
lemma " (! x . (~( P x =Q x) ))  =(! x . ( P x = (~ Q x )) )" by auto  
lemma " ~(! x . (( P x =Q x) ))  =(! x . ( P x = (~ Q x )) )" oops
lemma "(1::nat) : {x::nat . x=x}" by auto 

lemma "(! x . (P x) \<longrightarrow>  (Q x)) \<Longrightarrow>(! x . ~(Q x)\<longrightarrow> ~(P x)) " by auto

lemma "( ! x y::nat . x = y ) \<Longrightarrow> ( ! x y . \<not> (x = y) )"  by auto

lemma "( \<And> x y .x = ( y::nat) ) \<Longrightarrow> ( \<not> (x = y) )"  by auto

lemma "( x = ( y::nat) ) \<Longrightarrow> ( \<not> (x = y) )"  by sorry


lemma " ( \<And> x .P x) \<Longrightarrow> ( \<And> x. (\<And> x. P x) )" by auto

lemma " P \<Longrightarrow> (\<And> x. P)" by auto

lemma " P x \<Longrightarrow> (\<forall> x. P x)" by auto

lemma " f \<equiv> g \<Longrightarrow> f x \<equiv> g x" by auto

lemma "   f x \<equiv> g x \<Longrightarrow> f \<equiv> g" by auto
lemma " (\<And> x.  f x \<equiv> g x) \<Longrightarrow> f \<equiv> g" by auto

lemma " (\<And> x. P x) \<Longrightarrow> (P x)" by auto

lemma t1:"(PP::nat list\<Rightarrow> bool)[]" sorry

lemma t2:" (PP::nat list\<Rightarrow> bool)[] \<Longrightarrow> PP ( x#[])" sorry

lemma t3: "PP (x#[])"
proof -
  from t1 t2 show "PP(x#[])"  by auto
qed

lemma "\<And> x. PP (x#[])" by (auto simp add:t3)


lemma t4: "F x"  sorry

lemma t5: "\<And> x F .F x" using t4 by auto


lemma t6: "F x \<Longrightarrow> (\<And> F x . F x)" by auto

notepad
begin
  {
    assume " (x= (y::int))"
    then have "(1::int) =(2::int)" by auto
        
  have "!X Y.(X\<longrightarrow>Y) = ((~ X) \<or>Y) " by simp
  have "( (~(! x . A (x))) \<or> (? x . B( x)) ) = ( (! x .A (x) ) \<longrightarrow> (? x .B(x)) ) " by auto
}
  
end