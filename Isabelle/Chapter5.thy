(* Elaheh Ghassabani, University of Minnesota, Summer2015 *)

theory Chapter5
imports Main
begin





inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_0: "iter r 0 x x" |
iter_Suc: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"



lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof 
 assume 0: "surj f"
 from 0 have 1: "\<forall> A. \<exists> a. A = f a" by(simp add: surj_def)
 from 1 have 2: "\<exists> a. {x . x \<notin> f x} = f a" by blast
 from 2 show "False" by blast
qed



lemma fixes a b :: int assumes "b dvd (a + b)" shows "b dvd a"
proof -
{
fix k assume k: "a + b = b * k"
have "\<exists> k' . a = b * k'"
proof
show "a = b * (k -  1)" using k by (simp add: algebra_simps)
qed
}
then show ?thesis using assms by (auto simp add: dvd_def)
qed

 
lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" 
  and "A x y"
  shows "T x y"
 
proof (rule ccontr)
assume a: "\<not> T x y"
then have 1: "T y x" using T by auto
then have 2: "A y x" using TA by auto
hence "A x y \<and> A y x" using assms by auto
hence "x = y" using assms by auto
hence "T x y" using 1 by auto
(* hence "T x y \<and> \<not> T x y" using a by auto *)
thus "False" using a by auto
qed

(*
  do we have a keyword like sorry?!
*)

 
value "nat(97 mod 2)"
value "2 dvd (6::nat)"
lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs)
      \<or> (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof (cases "length xs mod 2") 
assume c1: "length xs mod 2 = 0"
then obtain ys zs where p: "ys = take ((length xs) div 2) xs \<and>
                         zs = drop (length ys) xs  " by auto
then have 1: "xs = ys @ zs"  by (metis append_eq_conv_conj append_take_drop_id)
from p have ly: " length ys =  ((length xs) div 2)" by auto
from p ly have lz: " length zs =  (length xs) - (length ys)" by auto
from ly lz p have eql : "length ys = length zs " using c1 by auto                     
from eql 1 show ?thesis by auto
next                         
fix n assume c2: "(length xs mod 2) = Suc n"
then obtain ys zs where q: "ys = take (Suc((length xs) div 2)) xs \<and>
                            zs = drop (length ys) xs "  by blast
then have 2: "xs = ys @ zs"  by (metis append_eq_conv_conj append_take_drop_id)
from q have ly': " length ys =   (Suc((length xs) div 2))" using c2 by auto
from q ly' have lz': " length zs =  (length xs) - (length ys)" by auto
from ly' lz' q have eql' : "length ys = length zs + 1 "
by (metis Suc_eq_plus1 add_diff_cancel_right' c2 diff_Suc_eq_diff_pred even_iff_mod_2_eq_zero mult_2 odd_two_times_div_two_nat old.nat.distinct(2))
from eql' 2  show ?thesis  using c2 by auto
qed


text{*
\exercise
Give a structured proof by rule inversion:
*}
inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun even :: "nat \<Rightarrow> bool" where
"even 0 = True" |
"even (Suc 0) = False" |
"even (Suc (Suc n)) = even n"

lemma ev1: "ev n \<Longrightarrow> even n"
proof (induction rule: ev.induct)
  case ev0
     show ?case by simp
next
  case evSS
     then show ?case by simp
qed

(*lemma ev2: "ev n \<Longrightarrow> even n"
proof (induction rule: ev.induct)
    let ?case = "even 0"
       show ?case by simp
next
    fix n assume evSS : "ev n \<Longrightarrow> even n"
                        "ev (Suc (Suc n))"
     let ?case = "even (Suc (Suc n))"
       then show ?case using evSS by simp
qed
 *)
(*
(*
lemma "ev n \<Longrightarrow> ev (n - 2)"*)
(*lemma assumes "ev n" shows "ev (n + 2)"*)
lemma assumes "ev n" shows "ev (n - 2)"
(*lemma assume "ev n" from this have "ev (n - 2)"*)
proof cases
  case ev0 thus "ev(n - 2)"  by (simp add: ev.ev0)
next
  case (evSS k) thus "ev(n - 2)"  by (simp add: ev.evSS)
qed
*)

lemma "\<not> ev (Suc 0)"
proof 
  assume "ev (Suc 0)"
 (* then show False by cases*)
  then show False using ev1 even.simps(2) by blast
qed



(*
lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof (induction "Suc m" arbitrary: m rule : ev.induct)
  fix m assume IH: "\<And> m. n = Suc m \<Longrightarrow> \<not> ev m"
  show "\<not> ev (Suc n)"
  proof (*- contradiction*)
  assume "ev(Suc n)"
  thus False
     proof cases (*- rule inversion*)
     fix k assume "n = Suc k" "ev k"
     thus False using IH by auto
     qed
   qed
qed
*)

(* my proof *)
lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof (induction "Suc m" arbitrary: m rule : ev.induct)
   case (evSS k)
   thus ?case  using ev.simps by blast
qed

lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
using assms ev.cases by auto
(*what is the difference between ev.cases and ev.simps?
  ev.simps: is like inversion on different induction rules
  ev.cases: rewrites the goal for each inductive rule
*) 
   

lemma "\<not> ev (Suc(Suc(Suc 0)))"
proof 
  assume 1: "ev (Suc(Suc(Suc 0)))"
  then show  False using ev1 even.simps(2) even.simps(3) by blast
(* how can I prove this by inversion ? *)
qed 


lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction arbitrary: n rule: iter.induct)
   case iter_0
      thus ?case by (simp add: star.refl)
   case iter_Suc
      thus ?case by (simp add: star.step)
qed

 


fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (h#t) = {h} \<union> elems t"

value "elems [1::int,3,3,5,6]"


(*
it comes easily from this old approach! ah!
lemma  "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
apply (induction xs)
apply auto
apply rule
apply fastforce
by (metis Un_iff append.simps(2) append_Nil  elems.simps(1) elems.simps(2) empty_iff insert_iff)
*)
lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
    thus ?case by auto
next
  fix h t case (Cons h t)
    then have 1: "(x = h) \<or> (x \<in> elems t \<and> x \<noteq> h)" by auto
    then show ?case
    proof
       assume xh: "x = h"
       then obtain ys zs where x1: "(ys::'a list) = [] \<and> (zs :: 'a list) = t" by auto
       then have ?case using 1 xh Cons.prems by fastforce
       then show ?thesis using 1  xh by auto
    next
        assume xt: "x  \<in> elems t  \<and> x \<noteq> h"
        from xt obtain ys' zs' where x2: "(ys':: 'a list) = h # t1 \<and> (zs' :: 'a list) = t2 " by simp
        then have ?case using xt Cons.IH using Cons_eq_appendI by force
        then show ?thesis using 1  xt by auto
    qed
qed
 
end

