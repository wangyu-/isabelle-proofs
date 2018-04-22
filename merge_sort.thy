(*<*) theory merge_sort imports Main begin (*>*)
  
fun le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "le a []     = True"
| "le a (x#xs) = (a <= x \<and> le a xs)"


fun sorted2 :: "nat list \<Rightarrow> bool" where 
"sorted2 [] = True "
| "sorted2 (x#[]) = True "
| "sorted2 (x#(y#r)) = ( x\<le>y \<and> sorted2 (y#r) )"

value "sorted [2::nat,1,3]"
  
primrec sorted :: "nat list \<Rightarrow> bool" where
  "sorted []     = True"
| "sorted (x#xs) = (le x xs \<and> sorted xs)"

lemma lemma_new2 :"(sorted2(x#y) \<Longrightarrow> le x y) \<Longrightarrow> ( sorted2 (x#a#y) \<Longrightarrow> le x (a#y) )"
proof -
  assume new3:"(sorted2(x#y) \<Longrightarrow> le x y)"
  assume new4:" sorted2 (x#a#y)"
  then have new5:"x\<le>a" by simp
  from new4 have "sorted2 (a#y)" by simp
  (* have  "a\<le>x \<Longrightarrow> le x y  \<Longrightarrow>  le a (x#y) "  using test1 by simp  *)  (* not in scope*)
  have "x\<le>a  \<Longrightarrow> sorted2 (a#y) \<Longrightarrow> sorted2 (x#y)" 
  proof (induct y)
    case Nil
    then show ?case by auto
    next
    case (Cons a y)
      then show ?case by simp
  qed
  from this new5 new4 have "sorted2 (x#y)" by simp
  then have "le x y" using new3 by simp
  from this new5 show "le x (a#y)" by simp
qed

lemma lemma1_2:"sorted2(x#y) \<Longrightarrow> le x y" 
proof -
  have 1:"sorted2(x#[]) \<Longrightarrow> le x []" by simp
  (*
  have 2:"(sorted2(x#y) \<Longrightarrow> le x y) \<Longrightarrow> ( sorted2 (a#x#y) \<Longrightarrow> le a (x#y) ) "  (*useless, failed attempt*)
  proof -
    assume 3:"(sorted2(x#y) \<Longrightarrow> le x y)"
    assume 4:" sorted2 (a#x#y)"
    then have 5:"a\<le>x " by simp
    from 4 have 6:"sorted2(x#y)" by simp
    from this 3 have 7:"le x y" by simp
    have test1:  "a\<le>x \<Longrightarrow> le x y  \<Longrightarrow>  le a (x#y) " 
    proof -
      have " a\<le> x \<Longrightarrow> le x y \<Longrightarrow> le a y"
      proof (induct y)
        case Nil
        then show ?case by simp
      next
        case (Cons a y)
        then show ?case by simp
      qed
      then show  "a\<le>x \<Longrightarrow> le x y  \<Longrightarrow>  le a (x#y) "  by simp
    qed
    from this  5 7 show  "le a (x#y)" by simp
  qed *)
  (*have new2 :"(sorted2(x#y) \<Longrightarrow> le x y) \<Longrightarrow> ( sorted2 (x#a#y) \<Longrightarrow> le x (a#y) )"  (*doest work ,have to move it out*)
  proof -
    assume new3:"(sorted2(x#y) \<Longrightarrow> le x y)"
    assume new4:" sorted2 (x#a#y)"
    then have new5:"x\<le>a" by simp
    from new4 have "sorted2 (a#y)" by simp
    (* have  "a\<le>x \<Longrightarrow> le x y  \<Longrightarrow>  le a (x#y) "  using test1 by simp  *)  (* not in scope*)
    have "x\<le>a  \<Longrightarrow> sorted2 (a#y) \<Longrightarrow> sorted2 (x#y)" 
    proof (induct y)
      case Nil
      then show ?case by auto
      next
      case (Cons a y)
        then show ?case by simp
    qed
    from this new5 new4 have "sorted2 (x#y)" by simp
    then have "le x y" using new3 by simp
    from this new5 show "le x (a#y)" by simp
  qed*)
  (*from new2 have "\<And> a x y. (sorted2(x#y) \<Longrightarrow> le x y) \<Longrightarrow> ( sorted2 (x#a#y) \<Longrightarrow> le x (a#y) )" by auto*)
  show "sorted2(x#y) \<Longrightarrow> le x y"
  proof (induct y)
    case Nil
    then show ?case by simp
  next
    case (Cons a y)
    from lemma_new2 show "\<And>a y. (sorted2 (x # y) \<Longrightarrow> le x y) \<Longrightarrow> sorted2 (x # a # y) \<Longrightarrow> le x (a # y)"
      by auto
  qed 
qed

    
lemma lemma1: "(sorted (x#y) \<Longrightarrow> sorted2 (x#y) ) \<Longrightarrow> (sorted (a#x#y) \<Longrightarrow> sorted2 (a#x#y))" by simp

lemma lemma2: "(sorted (x#y) \<longrightarrow> sorted2 (x#y) ) \<Longrightarrow> (sorted (a#x#y) \<longrightarrow> sorted2 (a#x#y)) " by simp  

lemma induct1: "\<And> P.  (P::nat list \<Rightarrow>bool) [] \<Longrightarrow> ( \<And> x. P (x#[])) \<Longrightarrow> ( \<And> a x y.( P (x#y) \<Longrightarrow> P (a#x#y) )) \<Longrightarrow> (\<And> l. P l) "  using sorted_wrt_induct by blast

(* same as induct1 *)
lemma induct1_2 : "  (P::nat list \<Rightarrow>bool) [] \<Longrightarrow> ( \<And> x. P (x#[])) \<Longrightarrow> ( \<And> a x y.( P (x#y) \<Longrightarrow> P (a#x#y) )) \<Longrightarrow> (\<And> l. P l) "  using sorted_wrt_induct by blast

definition PP :: "nat list \<Rightarrow>bool" where "(PP x) \<equiv>  (sorted x \<longrightarrow> sorted2 x)"

lemma lemma3: " \<And> a x y. PP(x#y) \<Longrightarrow> PP(a#x#y)" by (simp add: lemma2 PP_def)

lemma lemma4: "PP []" by (simp add: PP_def)

lemma lemma5: " \<And> x. PP (x#[])" by (simp add: PP_def)

(*
lemma lemma6: " sorted ll \<Longrightarrow> sorted2 ll"
proof -
  (* from lemma4 lemma5 lemma3 induct1 have 1: "\<And> l . PP(l)" by blast *)
  from induct1 lemma4 have " ( \<And> x. PP (x#[])) \<Longrightarrow> ( \<And> a x y.( PP (x#y) \<Longrightarrow> PP (a#x#y) )) \<Longrightarrow> (\<And> l. PP l)" by blast
  from this lemma5 have " ( \<And> a x y.( PP (x#y) \<Longrightarrow> PP (a#x#y) )) \<Longrightarrow> (\<And> l. PP l) " by simp
  from this lemma3 have " (\<And> l. PP l )" by simp
  then have "\<And> ll. sorted ll \<longrightarrow> sorted2 ll" by (simp add: PP_def)
  then show " sorted ll \<Longrightarrow> sorted2 ll" by simp
   (* then show ?thesis by simp *)  (* doesnt work *)
qed
*)

lemma lemma6_new_prex3:" le b (a#ll) \<longrightarrow> sorted2 (a#ll) \<longrightarrow> sorted2 (b # a#ll)"
  by simp

lemma lemma6_new_prex2:"le b ll \<longrightarrow> sorted2 ll \<longrightarrow> sorted2 (b #ll)"
proof (cases ll)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  from this lemma6_new_prex3 show ?thesis by simp
qed

lemma lemma6_new_pre: "(sorted ll \<Longrightarrow> sorted2 ll) \<Longrightarrow> sorted (a # ll) \<Longrightarrow> sorted2 (a # ll)"
proof -
  assume 1:"sorted ll \<Longrightarrow> sorted2 ll"
  assume 2:"sorted (a # ll)"
  from 2 have "sorted (ll)" by simp
  from this 1 have 4:"sorted2 ll" by simp
  from 2 have 3:"le a ll" by simp
  from 3 4 lemma6_new_prex2 show "sorted2 (a # ll) "by simp
qed

lemma lemma6_new: " sorted ll \<longrightarrow> sorted2 ll"
proof (induction ll)
  case Nil
  then show ?case by auto
next
  case (Cons a ll)
  from this lemma6_new_pre show ?case by simp 
qed

lemma lemma7_pre: "(sorted2 ll \<Longrightarrow> sorted ll) \<Longrightarrow> sorted2 (a # ll) \<Longrightarrow> sorted (a # ll)"
proof -
  assume 1:"(sorted2 ll \<Longrightarrow> sorted ll)"
  assume 2:"sorted2 (a # ll)"
  from 2 have 3:"(sorted2 ll)"
    by (metis sorted2.elims(3) sorted2.simps(3))
  from 1 3 have 4: "sorted ll" by simp
  from 2 lemma1_2 have "le a ll" by simp
  from this 4 show "sorted (a#ll)" by simp
qed
  

lemma lemma7: " sorted2 ll \<longrightarrow> sorted ll"
proof (induct ll)
case Nil
  then show ?case by simp
next
  case (Cons a ll)
  from this lemma7_pre show ?case by auto
qed

lemma lemma7_again: " sorted2 ll \<longrightarrow> sorted ll"
proof (rule list.induct)
  show "sorted2 [] \<longrightarrow> sorted []" by auto
next
  from lemma7_pre show "\<And>x1 x2. sorted2 x2 \<longrightarrow> sorted x2 \<Longrightarrow> sorted2 (x1 # x2) \<longrightarrow> sorted (x1 # x2)"
    by auto
qed

lemma sort_eq: "sorted2 = sorted"
proof -
  from lemma7_again lemma6_new show  "sorted2 = sorted" by auto
qed

  
primrec count :: "nat list => nat => nat" where
  "count []     y = 0"
| "count (x#xs) y = (if x=y then Suc(count xs y) else count xs y)"
  
fun
 merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
 "merge [] ys = ys" |
 "merge xs [] = xs" |
 "merge (x # xs) (y # ys) = (
   if x \<le> y
     then x # merge xs (y # ys)
     else y # merge (x # xs) ys
 )"

fun
 msort :: "nat list \<Rightarrow> nat list"
where
 "msort [] = []" |
 "msort [x] = [x]" |
 "msort xs = (
   let half = length xs div 2 in
   merge (msort (take half xs)) (msort (drop half xs))
 )"

lemma le_lemma: " le a x\<Longrightarrow> le a y \<Longrightarrow> le a (merge x y) " 
proof (induct x y rule:merge.induct) 
  show " \<And>ys. le a [] \<Longrightarrow> le a ys \<Longrightarrow> le a (merge [] ys)" by auto
next
  show " \<And>v va. le a (v # va) \<Longrightarrow> le a [] \<Longrightarrow> le a (merge (v # va) [])" by auto
next 
  show "\<And>x xs y ys.
       (x \<le> y \<Longrightarrow> le a xs \<Longrightarrow> le a (y # ys) \<Longrightarrow> le a (merge xs (y # ys))) \<Longrightarrow>
       (\<not> x \<le> y \<Longrightarrow> le a (x # xs) \<Longrightarrow> le a ys \<Longrightarrow> le a (merge (x # xs) ys)) \<Longrightarrow>
       le a (x # xs) \<Longrightarrow> le a (y # ys) \<Longrightarrow> le a (merge (x # xs) (y # ys))" by auto
qed

(* interesting but not needed
lemma le_lemma_inv: " le a (merge x y) \<Longrightarrow> le a x" sorry

lemma le_lemma_inv2:  " le a (merge x y) \<Longrightarrow> le a y" sorry
*)

lemma  le_lemma2: "a\<le> x \<Longrightarrow> le x y \<Longrightarrow> le a y"
proof (induct y)
  case Nil
  then show ?case by simp
next
  case (Cons a y)
  then show ?case by auto
qed

lemma sort_merge_pre: " (x \<le> y \<Longrightarrow> sorted2 xs \<longrightarrow> sorted2 (y # ys) \<longrightarrow> sorted2 (merge xs (y # ys))) \<Longrightarrow>
       (\<not> x \<le> y \<Longrightarrow> sorted2 (x # xs) \<longrightarrow> sorted2 ys \<longrightarrow> sorted2 (merge (x # xs) ys)) \<Longrightarrow>
       sorted2 (x # xs) \<Longrightarrow> sorted2 (y # ys) \<Longrightarrow> sorted2 (merge (x # xs) (y # ys))"
proof -
  assume  1:"(x \<le> y \<Longrightarrow> sorted2 xs \<longrightarrow> sorted2 (y # ys) \<longrightarrow> sorted2 (merge xs (y # ys)))"
  from this sort_eq have new1: "(x \<le> y \<Longrightarrow> sorted xs \<longrightarrow> sorted (y # ys) \<longrightarrow> sorted (merge xs (y # ys)))" by simp
  assume  2:" (\<not> x \<le> y \<Longrightarrow> sorted2 (x # xs) \<longrightarrow> sorted2 ys \<longrightarrow> sorted2 (merge (x # xs) ys))"
  from this sort_eq have new2: " (\<not> x \<le> y \<Longrightarrow> sorted (x # xs) \<longrightarrow> sorted ys \<longrightarrow> sorted (merge (x # xs) ys))" by simp
  assume  3:"sorted2 (x # xs) "
  from this sort_eq have new3: "sorted (x#xs)" by simp
  assume  4:"sorted2 (y # ys) "
  from this sort_eq have new4: "sorted (y#ys)" by simp
  from new3 have new5:"le x xs" by auto
  from new4 have new6:"le y ys" by auto
  from new3 have new3_2:"sorted xs" by simp
  from new4 have new4_2:"sorted ys" by simp
  have new_goal: "sorted (merge (x # xs) (y # ys))" 
  proof (cases)
    assume 5:"x\<le>y"
    from this new1  have " sorted xs \<longrightarrow> sorted (y # ys) \<longrightarrow> sorted (merge xs (y # ys))" by simp
    from this new3_2 new4 have key:"sorted (merge xs (y # ys))" by simp
    from this have "sorted ( x #(merge xs (y # ys)) )" 
    proof -
      have "le x ys" using 5 new6 le_lemma2 by simp
      from this have "le x (y#ys)" using 5 by simp
      from this new5 le_lemma have "le x (merge xs (y # ys))" by simp
      from this key show "sorted ( x #(merge xs (y # ys)) )" by simp
    qed
    from this 5 show  "sorted (merge (x # xs) (y # ys))" by simp
    next
    assume 5:"\<not> x\<le>y " 
    from this new2 have " sorted (x # xs) \<longrightarrow> sorted ys \<longrightarrow> sorted(merge (x # xs) ys)" by simp
    from this new3 new4_2 have key:" sorted(merge (x # xs) ys) " by simp
    from 5 have 55:"y \<le> x" by simp
    have "sorted ( y # merge (x # xs) ys )"
    proof -
      have "le y xs" using 55 new5 le_lemma2 by simp
      from this have "le y (x#xs)" using 55 by simp
      from this new6 le_lemma have "le y (merge (x # xs) ys) " by simp
      from this key show "sorted ( y # merge (x # xs) ys )" by simp
    qed
    from this 5 show  "sorted (merge (x # xs) (y # ys))" by simp
  qed
  from this sort_eq show    "sorted2 (merge (x # xs) (y # ys))"  by simp
  (*  failed
  proof (cases) 
    assume 5:"x\<le>y"
    from 5 1 have 6:"(sorted2 xs \<longrightarrow> sorted2 (y # ys) \<longrightarrow> sorted2 (merge xs (y # ys)))" by simp
    from 5 have "merge (x # xs) (y # ys )  = x # merge xs (y # ys) " by simp
    from 3 sorted2_lemma have "sorted2 (xs)" by simp
    from this 4 6 have 7: " sorted2 (merge xs (y # ys)) " by simp
    from this have "sorted2 ( x # merge xs (y # ys) )" 
    proof (cases xs)
      case Nil
      from this 7 show "sorted2 ( x # merge xs (y # ys) )"  sorry
    next
      case (Cons a list)
      show "sorted2 ( x # merge xs (y # ys) )"
      proof 
        case "a< y"
        short
    qed
    from 5 this show "sorted2 (merge (x # xs) (y # ys))" by simp
    next
    assume "\<not> x\<le>y "
    show  "sorted2 (merge (x # xs) (y # ys))" sorry
  qed
  *)
qed

lemma lemma_final_pre:" sorted2 a \<longrightarrow> sorted2 b \<longrightarrow> sorted2 (merge a b )"
proof (induction a b rule: merge.induct)
  show "\<And>ys. sorted2 [] \<longrightarrow> sorted2 ys \<longrightarrow> sorted2 (merge [] ys)" by auto
next 
  show "\<And>v va. sorted2 (v # va) \<longrightarrow> sorted2 [] \<longrightarrow> sorted2 (merge (v # va) [])" by auto
next
  show "\<And>x xs y ys.
       (x \<le> y \<Longrightarrow> sorted2 xs \<longrightarrow> sorted2 (y # ys) \<longrightarrow> sorted2 (merge xs (y # ys))) \<Longrightarrow>
       (\<not> x \<le> y \<Longrightarrow> sorted2 (x # xs) \<longrightarrow> sorted2 ys \<longrightarrow> sorted2 (merge (x # xs) ys)) \<Longrightarrow>
       sorted2 (x # xs) \<longrightarrow> sorted2 (y # ys) \<longrightarrow> sorted2 (merge (x # xs) (y # ys))"    
    using sort_merge_pre by simp
qed

(*
theorem lemma_final2:"sorted2 (msort ll)"  (is ?test_is) 
proof (induct ll rule: msort.induct)
  show "sorted2 (msort [])" by simp
next
  show "\<And>x. sorted2 (msort [x])" by simp
next
  show "\<And>v vb vc.
       (\<And>x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (msort (take x (v # vb # vc)))) \<Longrightarrow>
       (\<And>x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (msort (drop x (v # vb # vc)))) \<Longrightarrow>
       sorted2 (msort (v # vb # vc))" using lemma_final_pre by simp
qed
*)

lemma lemma_final2_again:"sorted2 (msort ll)"  (is ?test_is)   (*manually ,by metis *)
proof (induct ll rule: msort.induct)
  show "sorted2 (msort [])" by simp
next
  show "\<And>x. sorted2 (msort [x])" by simp
next
  show "\<And>v vb vc.
       (\<And>x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (msort (take x (v # vb # vc)))) \<Longrightarrow>
       (\<And>x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (msort (drop x (v # vb # vc)))) \<Longrightarrow>
       sorted2 (msort (v # vb # vc))" 
  proof -
    fix v vb vc 
    show  "(\<And>x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (msort (take x (v # vb # vc)))) \<Longrightarrow>
       (\<And>y. y = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (msort (drop y (v # vb # vc)))) \<Longrightarrow>
       sorted2 (msort (v # vb # vc))"
    proof -
    assume 1:" (\<And>x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (msort (take x (v # vb # vc))))"
    assume 2:"(\<And>y. y = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (msort (drop y (v # vb # vc))))"
    obtain z where z:"z =  length (v # vb # vc) div 2 " by simp
    from z 1 have 3:"sorted2 (msort (take z (v # vb # vc)))" by simp
    from z 2 have 4:"sorted2 (msort (drop z (v # vb # vc)))" by simp
    from z have "msort (v # vb # vc)  = merge (msort (take z (v#vb#vc))) (msort (drop z (v#vb#vc)))" by simp
    from this 3 4 lemma_final_pre show "sorted2 (msort (v # vb # vc))" by metis
  qed
qed
qed



(* failed attemp bc of didnt use "induct ll"
lemma lemma_final:"sorted2 (msort ll)" 
proof (induct rule: msort.induct)
  show "sorted2 []" by simp
next
  show "\<And>x. sorted2 [x]" by simp
next

  show "\<And>v vb vc.
       (\<And>x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (take x (v # vb # vc))) \<Longrightarrow>
       (\<And>y. y = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (drop y (v # vb # vc))) \<Longrightarrow> sorted2 (v # vb # vc)"
  proof -
    fix v vb vc 
    show  "
       (\<And> x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (take x (v # vb # vc))) \<Longrightarrow>
       (\<And> y. y = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (drop y (v # vb # vc))) \<Longrightarrow> sorted2 (v # vb # vc)" 
    proof -
      assume  1:"(\<And> x. x = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (take x (v # vb # vc)))"
      then have 2:"  sorted2 (take ( length (v # vb # vc) div 2) (v # vb # vc))" by simp
      assume  3:"\<And> y. y = length (v # vb # vc) div 2 \<Longrightarrow> sorted2 (drop y (v # vb # vc))"
      then have 4:" sorted2 (drop ( length (v # vb # vc) div 2) (v # vb # vc)) " by simp
      obtain z where z:"z =  length (v # vb # vc) div 2 " by simp
      from 1 2 z have 5:"sorted2 (take z (v # vb # vc))" by simp
      from 3 4 z have 6:"sorted2 (drop z (v # vb # vc))" by simp
      from z 5 6 have "sorted2 (v # vb # vc) " sorry
      from this show " sorted2 (v # vb # vc)" by simp
  qed
qed
*)
lemma count_lemma0:"count (merge xs ys) x = (count xs x) + (count ys x)"
proof (induct xs ys rule:merge.induct)
  show "\<And>ys. count (merge [] ys) x = count [] x + count ys x" by auto
next
  show "\<And>v va. count (merge (v # va) []) x = count (v # va) x + count [] x" by auto
next 
  show "\<And>xa xs y ys.
       (xa \<le> y \<Longrightarrow> count (merge xs (y # ys)) x = count xs x + count (y # ys) x) \<Longrightarrow>
       (\<not> xa \<le> y \<Longrightarrow> count (merge (xa # xs) ys) x = count (xa # xs) x + count ys x) \<Longrightarrow>
       count (merge (xa # xs) (y # ys)) x = count (xa # xs) x + count (y # ys) x " by auto
qed

(*
lemma count_lemma1: "count xs x = (count (take n xs) x)  + (count (drop n xs) x)"
proof (induct xs) 
  show " count [] x = count (take n []) x + count (drop n []) x" by auto
next 
  show "\<And>a xs. count xs x = count (take n xs) x + count (drop n xs) x \<Longrightarrow>
            count (a # xs) x = count (take n (a # xs)) x + count (drop n (a # xs)) x " 
    sorry
qed
*)

lemma count_lemma_cat: "count (xs @ ys) x = (count xs x)  + (count ys x)" 
proof (induct xs)
  show "count ([] @ ys) x = count [] x + count ys x" by auto
next
  show "\<And>a xs. count (xs @ ys) x = count xs x + count ys x \<Longrightarrow>
            count ((a # xs) @ ys) x = count (a # xs) x + count ys x" by auto
qed

lemma cat_lemma: " xs = (take n xs) @ (drop n xs)"
proof (induct xs)
  show "[] = take n [] @ drop n []" by auto
next 
  show "\<And>a xs. xs = take n xs @ drop n xs \<Longrightarrow> a # xs = take n (a # xs) @ drop n (a # xs) "
    by auto
qed

lemma count_lemma11:  "count xs x = (count (take n xs) x)  + (count (drop n xs) x)" (is "?P" )
proof -
  show "?P" using count_lemma_cat cat_lemma by metis
qed

theorem "sorted (msort ll)"
proof -
  show "sorted (msort ll)" using lemma_final2_again sort_eq by simp
qed 

theorem "sorted2 (msort ll)"
proof -
  show "sorted2 (msort ll)" using lemma_final2_again by simp
qed

theorem "count (msort xs) x = count xs x" (is "?P" )
proof (induct xs rule:msort.induct)
  show "count (msort []) x = count [] x" by auto
next
  show "\<And>xa. count (msort [xa]) x = count [xa] x" by auto
next
  show "\<And>v vb vc.
       (\<And>xa. xa = length (v # vb # vc) div 2 \<Longrightarrow>
              count (msort (take xa (v # vb # vc))) x = count (take xa (v # vb # vc)) x) \<Longrightarrow>
       (\<And>xa. xa = length (v # vb # vc) div 2 \<Longrightarrow>
              count (msort (drop xa (v # vb # vc))) x = count (drop xa (v # vb # vc)) x) \<Longrightarrow>
       count (msort (v # vb # vc)) x = count (v # vb # vc) x "
    using count_lemma11 count_lemma0 by simp
qed

