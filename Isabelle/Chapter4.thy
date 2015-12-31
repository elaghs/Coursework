(* Elaheh Ghassabani, University of Minnesota, Summer2015 *)

theory Chapter4
imports "~~/src/HOL/IMP/ASM"
begin
(*what does this exactly mean?! "for r where" ?!!!! *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

text{*
\section*{Chapter 4}

\exercise
Start from the data type of binary trees defined earlier:
*}

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text{*
An @{typ "int tree"} is ordered if for every @{term "Node l i r"} in the tree,
@{text l} and @{text r} are ordered
and all values in @{text l} are @{text "< i"}
and all values in @{text r} are @{text "> i"}.
Define a function that returns the elements in a tree and one
the tests if a tree is ordered:
*}

fun set :: "'a tree \<Rightarrow> 'a set"  where
"set Tip = {}" |
"set (Node t a t') = (set t \<union> {a} \<union> set t')  "

value "set (Node (Node (Node Tip (5::int) Tip) 3 (Node Tip 0 Tip )) 1 (Node Tip 4 Tip))"

(*fun ord :: "int tree \<Rightarrow> bool"  where
"ord Tip = True" |
"ord (Node t a t') = (ord t \<and> 
                      (card {y . y \<in> (set t) \<and> a > y } = card (set t)) \<and> 
                      (card {y . y \<in> (set t') \<and> a < y } = card (set t')) \<and> 
                      ord t' )"
*)
fun ord :: "int tree \<Rightarrow> bool"  where
  "ord Tip = True" | 
  "ord (Node t a t') = ((ord t) \<and> (ord t') \<and> 
     (\<forall> x \<in> (set t) . (x < a)) \<and> 
     (\<forall> x \<in> (set t') . (a < x)))"

text{* Hint: use quantifiers.

Define a function @{text ins} that inserts an element into an ordered @{typ "int tree"}
while maintaining the order of the tree. If the element is already in the tree, the
same tree should be returned.
*}

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree"  where
"ins a Tip = Node Tip a Tip" |
"ins a (Node t e t') =  (if (a = e) then (Node t e t')
                         else if (a > e) then (Node t e (ins a t'))
                         else (Node (ins a t) e t'))"

value "set (Node (Node (Node Tip (5::int) Tip) 3 (Node Tip 0 Tip )) 1 (Node Tip 4 Tip))"
(* order: in order*)
value "ord (Node (Node (Node Tip (1::int) Tip) 3 (Node Tip 8 Tip )) 9 (Node Tip 10 Tip))"
(* set: pre order *)
value "set (Node (Node (Node Tip (1::int) Tip) 3 (Node Tip 8 Tip )) 9 (Node Tip 10 Tip))"
value "(ins 0 (Node (Node (Node Tip (1::int) Tip) 3 (Node Tip 8 Tip )) 9 (Node Tip 10 Tip)))"
value "(ins 7 (Node (Node (Node Tip (1::int) Tip) 3 (Node Tip 8 Tip )) 9 (Node Tip 10 Tip)))"
value "(ins (-1) (Node (Node (Node Tip (1::int) Tip) 3 (Node Tip (-2) Tip )) 9 (Node Tip 11 Tip)))"

text{* Prove correctness of @{const ins}: *}

value "set (Chapter4.ins (-2) (Node Tip (- 2) (Node Tip (- 1) Tip)))"

lemma set_ins [simp]: "set(ins x t) = {x} \<union> set t"
apply (induction t)
apply (auto)
done

theorem ord_ins [simp]: "ord t \<Longrightarrow> ord(ins i t)"
apply (induction  t)
apply (auto)
done

text{*
\endexercise

\exercise
Formalize the following definition of palindromes
\begin{itemize}
\item The empty list and a singleton list are palindromes.
\item If @{text xs} is a palindrome, so is @{term "a # xs @ [a]"}.
\end{itemize}
as an inductive predicate
*}

inductive palindrome :: "'a list \<Rightarrow> bool" where
pal_emp: "palindrome []" |
pal_single: "palindrome [a]" |
pal_cons: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a]) "

text {* and prove *}

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
apply (induction xs rule: palindrome.induct)
apply (auto)
done

text{*
\endexercise

\exercise
We could also have defined @{const star} as follows:
*}

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

text{*
The single @{text r} step is performer after rather than before the @{text star'}
steps. Prove
*}
(* thm step *)
lemma r_star : "r x y \<Longrightarrow> star r x y"
apply (rule step)
apply (auto)
apply (rule refl)
done 

 
lemma step_star :  "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z "
apply (induction rule: star.induct)
apply (auto simp add: r_star)
apply (rule step)
apply (auto)
done

lemma sp_s: "star' r x y \<Longrightarrow> star r x y"
apply (induction  rule:star'.induct)
apply (rule refl)
apply (auto dest: step_star)
done

lemma r_star' : "r x y \<Longrightarrow> star' r x y"
apply (rule step')
apply (auto)
apply (rule refl')
done 
(* we can do induction only on the last prem*)
lemma step_star' : "r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
apply (rotate_tac 1)
apply (induction rule: star'.induct)
apply (auto simp add: r_star')
apply (rule step')
apply auto 
done
 thm star'.intros
lemma s_s' : "star r x y \<Longrightarrow> star' r x y" 
apply (induction rule: star.induct)
apply (rule refl')
(*apply (drule ste_star)*)
apply (auto dest: step_star')
(*apply (subgoal_tac "star r x y")
apply (drule sp_s) *)
done

 

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
one_elem : "iter r 0 x0 x0" |
s_elem: "iter r n x0 xsi \<Longrightarrow> r xsi xssi \<Longrightarrow> iter r (Suc n) x0 xssi"

text{*
Correct and prove the following claim:
*}
thm s_elem
lemma s_el [simp] : "r x y \<Longrightarrow> iter r n z x \<Longrightarrow> iter r (Suc n) z y"
apply rule
apply (auto)
done

lemma "iter r n x y \<Longrightarrow> star r x y"
apply (induction rule: iter.induct)
apply (rule refl)
apply (rule step_star)
apply (auto)
done


 

datatype alpha = asym | bsym

inductive S :: "alpha list \<Rightarrow> bool" where
S_eps: "S []" |
S_gen: "S w \<Longrightarrow> S (asym # w @ [bsym])" |
S_s  : "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
T_eps: "T []" |
T_gen: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ asym # w2 @ [bsym])" 

lemma TS: "T w \<Longrightarrow> S w"
apply (induction rule: T.induct)
apply (rule)
apply (auto intro: S.intros)
done

lemma T_gen_emp : "T [] \<Longrightarrow> T w2 \<Longrightarrow> T ([]@asym # w2 @ [bsym])"
apply (rule)
apply (auto)
done
lemma T_gen_emp2 : "T ([]@asym # w2 @ [bsym]) \<Longrightarrow> T (asym # w2 @ [bsym])"
apply (auto)
done
lemma T_app' [simp] : "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1@w2) \<Longrightarrow> T (w1 @ asym # w2 @ [bsym]) "
apply rule
apply auto
done
 
thm T_gen
lemma app_simp: 
"T ((w1 @ w1a) @ alpha.asym # w2 @ [bsym]) \<Longrightarrow> T (w1 @ w1a @ alpha.asym # w2 @ [bsym])"
apply simp
done
lemma T_app : "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1@w2)"
apply (rotate_tac 1)
apply (induct rule: T.induct)
apply auto
apply (rule app_simp)
apply (rule T_gen)
apply auto
done

lemma ST: "S w \<Longrightarrow> T w"
apply (induction rule: S.induct)
apply (auto intro: T.intros)
apply (rule T_gen_emp2)
apply (rule)
apply (auto)
apply (rule T_eps)
apply (rule T_app)
apply auto 
done

corollary SeqT: "S w \<longleftrightarrow> T w"
apply rule
apply (rule ST)
apply assumption
apply (rule TS)
apply assumption
done




inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
aval_N: "aval_rel (N n) s n" |
aval_V: "aval_rel (V x) s (s x)" |
aval_P: "aval_rel a s a_val \<Longrightarrow> aval_rel b s b_val \<Longrightarrow> aval_rel (Plus a b) s (a_val + b_val)"

lemma aval_rel_aval: "aval_rel a s v \<Longrightarrow> aval a s = v"
apply (induction rule: aval_rel.induct)
apply (auto)
done

lemma aval_aval_rel: "aval a s = v \<Longrightarrow> aval_rel a s v"
apply (induction arbitrary: v rule: aval.induct)
apply (auto)
apply (rule)
apply (rule)
apply (rule)
apply (auto)
done

corollary "aval_rel a s v \<longleftrightarrow> aval a s = v"
apply rule
apply (rule aval_rel_aval)
apply (assumption)
apply (rule aval_aval_rel)
apply (assumption)
done




inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
ok_nil:  "ok n [] n" | 
ok_loadi:"ok (Suc n) is m \<Longrightarrow> ok n ((LOADI _) # is) m" |
ok_load: "ok (Suc n) is m \<Longrightarrow> ok n ((LOAD _) # is) m" |
ok_add:  "ok (Suc n) is m \<Longrightarrow> ok (Suc (Suc n)) (ADD # is) m"

 
lemma [simp, intro] : "ok 0 [LOAD x] (Suc 0) "
apply (rule)
apply rule
done 

lemma [simp, intro]: "ok 0 [LOAD x, LOADI v, ADD] (Suc 0)"
apply (rule)
apply (rule)
apply (rule )
apply (rule)
done 

lemma [simp, intro]: "ok (Suc (Suc 0)) [LOAD x, ADD, ADD, LOAD y] (Suc (Suc 0))"
apply (rule)
apply rule
apply rule
apply rule
apply rule
done
 

lemma [simp, intro]: "\<lbrakk>ok n is n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec is s stk) = n'"
apply (induction arbitrary: stk rule: ok.induct)
apply auto 
done

text {*
Prove that instruction sequences generated by @{text comp}
cannot cause stack underflow: \ @{text "ok n (comp a) ?"} \ for
some suitable value of @{text "?"}.
\endexercise
*}



lemma ok_concat: " ok n l1 n1 \<Longrightarrow>  ok n1 l2 n2  \<Longrightarrow> ok n (l1 @ l2) n2"
apply (induction rule: ok.induct)
apply (auto intro: ok.intros)
done
 

lemma app_ord : "ok n ((a @ b) @ c) (Suc n) \<Longrightarrow> ok n (a @ b @ c) (Suc n)"
apply auto
done
thm app_ord
lemma "ok n (comp a) (Suc n)"
apply (induction arbitrary: n  rule: comp.induct)
apply (auto intro: ok.intros)
apply (rule ok_concat)
apply auto
apply (rule ok_concat)
apply assumption
apply rule
apply rule
done
end

