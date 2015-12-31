(* Elaheh Ghassabani, University of Minnesota, Summer2015 *)
theory Chapter2
imports Main
begin

text{*
\section*{Chapter 2}

\exercise
Use the \textbf{value} command to evaluate the following expressions:
*}

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"
value "[a,b] @ [c,d]"

text{*
\endexercise


\exercise
Recall the definition of our own addition function on @{typ nat}:
*}

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

text{*
Prove that @{const add} is associative and commutative.
You will need additional lemmas.
*}

lemma add_assoc: "add (add m n) p = add m (add n p)"
apply (induction m)
apply (auto)
done

lemma add_0 [simp] : "add a 0 = a"
apply (induction a)
apply (auto)
done
lemma suc_add  [simp] : "Suc (add a b) = add a (Suc b)"
apply (induction a)
apply (auto)
done

lemma add_comm: "add m n = add n m"
apply (induction m)
apply (auto)
done

text{* Define a recursive function *}

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc (Suc (double m)) "

value "double 4"


text{* and prove that *}

lemma double_add: "double m = add m m"
apply (induction m)
apply (auto)
done
text{*
\endexercise


\exercise
Define a function that counts the number of occurrences of
an element in a list:
*}

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count Nil a = 0" |
"count (Cons h t) a = (if a = h then Suc (count t a) else count t a)"

text {*
Test your definition of @{term count} on some examples.
Prove the following inequality:
*}

theorem "count xs x \<le> length xs"
apply (induction xs)
apply (auto)
done

text{*
\endexercise


\exercise
Define a function @{text snoc} that appends an element to the end of a list.
Do not use the existing append operator @{text "@"} for lists.
*}

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
(*"snoc (Cons h t) a = h # t @ [a]"*)
"snoc (Cons h t) a = h # (snoc t a)"

value "snoc [n,m,v] c"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (Cons h t) = snoc (reverse t) h"

fun reverse_with_app :: "'a list \<Rightarrow> 'a list" where
"reverse_with_app Nil = Nil" |
"reverse_with_app (Cons h t) =  (reverse_with_app t)@(Cons h Nil) "

value "reverse [a,b,x]"

lemma rev_snoc [simp]: "reverse (snoc l a) = a # reverse l "
apply (induction l)
apply (auto)
done 
theorem "reverse (reverse xs) = xs"
apply (induction xs)
apply (auto)
done
text{*
\endexercise


\exercise
The aim of this exercise is to prove the summation formula
\[ \sum_{i=0}^{n}i = \frac{n(n+1)}{2} \]
Define a recursive function @{text "sum n = 0 + ... + n"}:
*}

fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc m) = (Suc m) + sum m"


lemma "sum n = n * (n+1) div 2"
apply (induction n)
apply (auto)
done

text{*
\endexercise


\exercise
Starting from the type @{text "'a tree"} defined in the text, define
a function that collects all values in a tree in a list, in any order,
without removing duplicates.
*}
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = a #(contents l @ contents r)"

text{*
Then define a function that sums up all values in a tree of natural numbers
*}

fun treesum :: "nat tree \<Rightarrow> nat" where
"treesum Tip = 0" |
"treesum (Node l n r) = n + treesum l + treesum r "

lemma "treesum t = listsum(contents t)"
apply (induction t)
apply (auto)
done

text{*
\endexercise

\exercise
Define a new type @{text "'a tree2"} of binary trees where values are also
stored in the leaves of the tree.  Also reformulate the
@{text mirror} function accordingly. Define two functions *}

datatype 'a tree2 = Tip 'a | Node 'a "'a tree2" "'a tree2"  

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip a) = Tip a" |
"mirror (Node a x y) = Node a (mirror y) (mirror x)"

value "Node a (Node b c (Node d e f))(Node g (Node h i j) k)"
value "mirror (Node a (Node b c (Node d e f))(Node g (Node h i j) k))"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip a) = [a]" |
"pre_order (Node a x y) = a # (pre_order x @ pre_order y)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip a) = [a]" |
"post_order (Node a x y) = (post_order x)@(post_order y)@[a]"

lemma "pre_order (mirror t) = rev (post_order t)"
apply (induction t)
apply (auto)
done

text{*
\endexercise

\exercise
Define a recursive function
*}

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (Cons h t) = (if (t=[]) then [h] else  (h # (a#(intersperse a t))))"
(* induct xs rule : interperse.induct*)
value "intersperse xxx [t,c,z,d,f]"
lemma map_f :  "map f (a#l) = (f a)#(map f l)"
apply (induction l)
apply (auto)
done
 
lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply (induction xs)
apply(auto)
done

text{*
\endexercise


\exercise
Write a tail-recursive variant of the @{text add} function on @{typ nat}:
*}

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"
value "itadd 3 2"

lemma "itadd m n = add m n"
apply (induction m arbitrary: n)
apply (auto)
done

text{*
\endexercise


\exercise\label{exe:tree0}
Define a datatype @{text tree0} of binary tree skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function that counts the number of all nodes (inner nodes and leaves)
in such a tree:
*}
datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + nodes l + nodes r"

value "Node (Node (Node Tip Tip)(Tip))(Tip)"
value "nodes (Node (Node (Node Tip Tip)(Tip))(Tip))"


fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"
value "nodes(explode 1 (Node (Node Tip Tip) Tip))" (*5\<longrightarrow>11     n * 2\<and>e + (2\<and>e  - 1)*)
value "nodes(explode 2 (Node Tip Tip))" (*3\<longrightarrow>15*)
value "nodes(explode 2 (Node (Node Tip Tip) Tip))" (*5\<longrightarrow>23 *)
value "nodes(explode 3 (Node Tip Tip))" (*3\<longrightarrow>31*)

lemma count_exploded : "nodes (explode e t) = (nodes t) * (2^e) + ((2^e) - 1)"
apply (induction e arbitrary:t)
apply (auto simp add : algebra_simps)
done


text{*

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
*}

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text{*
Define a function @{text eval} that evaluates an expression at some value:
*}

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const n) x = n" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x) " 

value "Add (Mult (Mult (Const 2) Var) Var) (Const 3)"
value "Mult (Add (Mult (Const 2) Var) Var) (Const 3)"
value "eval(Mult (Add (Mult (Const 2) Var) Var) (Add (Mult Var Var)(Const 3)) ) i"
value "eval (Add (Mult (Const 2) Var) (Const 3)) i"
value "eval (Add (Mult (Mult (Const 2) Var) Var) (Const 3)) i"
value "eval (Add (Mult (Mult (Const 2) Var) Var) (Const 3)) 1"
text{*
For example, @{prop"eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"}.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function @{text evalp} that evaluates a polynomial at a given value:
*}
(*
fun evalp0 :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp0 [] x = 0" |
"evalp0 (h#t) x = h * (x ^ (length t)) + evalp0 t x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp l x = evalp0 (rev l)x"
*)
fun evalp0 :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
"evalp0 [] p x = 0" |
"evalp0 (h#t) p x = h * (x^p) + (evalp0 t (Suc p) x)"
fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp c x = evalp0 c 0 x"

value "evalp [2,3,4] x"
text{*
Define a function @{text coeffs} that transforms an expression into a polynomial.
This will require auxiliary functions.
*}
(*
fun sort_helper :: "(int*int) \<Rightarrow> (int*int) list \<Rightarrow> (int*int)list" where
"sort_helper a [] = [a]"|
"sort_helper (c,p)((ch,ph)#t) = (if (p \<le> ph) then (c,p)#((ch,ph)#t) 
                                else (ch,ph)# sort_helper (c,p)t)"
fun sort :: "(int*int) list \<Rightarrow> (int*int)list" where
"sort [] = []" |
"sort (h#t) = sort_helper h (sort t)"

value "sort [(5,9),(2,1),(3,7),(3,0)]"
fun add_helper :: "(int*int) list \<Rightarrow> (int*int)list" where
"add_helper [] = []" | 
"add_helper [a] = [a]" |
"add_helper ((c1,p1)#((c2,p2)#t)) = (if (p1 = p2) then (c1+c2, p1)#add_helper t 
                                     else (c1, p1)# add_helper((c2, p2)#t))"
fun mult_helper :: "(int*int) list \<Rightarrow> (int*int)list \<Rightarrow> (int*int)list" where
"mult_helper l[] = []" |
"mult_helper []l = []" | 
"mult_helper ((c1,p1)#t1)((c2,p2)#t2) = 
            ((c1*c2,p1+p2)#mult_helper [(c1,p1)] t2)@ mult_helper t1 ((c2,p2)#t2)"
value "mult_helper [(1,0),(2,3),(1,2)][(2,1),(2,0)]"

fun reduc_exp :: "exp \<Rightarrow> (int*int) list \<Rightarrow>  (int*int) list" where
(* (cof, pow) op = n \<Rightarrow> noun, op = a \<Rightarrow> add, op = m \<Rightarrow>mult *)
"reduc_exp (Mult Var Var) l = (1, 2)#l" |
"reduc_exp Var l  = (1,1)#l" |
"reduc_exp (Add Var Var) l  = (2, 1)#l " |
"reduc_exp (Mult (Const n) Var) l  = (n,1)#l" |
"reduc_exp (Mult Var (Const n)) l  = (n,1)#l" |
"reduc_exp (Add (Const n) Var) l  = (n,0)#((1,1)#l)" |
"reduc_exp (Add Var (Const n)) l  = (n,0)#((1,1)#l)" |
"reduc_exp (Const n) l  = (n, 0)#l" |
"reduc_exp (Add x y) l = add_helper(sort ((reduc_exp x l) @ (reduc_exp y l)))" |
"reduc_exp (Mult x y)l = mult_helper (reduc_exp x l)(reduc_exp y l)"

value "eval(Add(Mult (Add (Const 2) Var) (Add (Mult Var Var)(Const 3))) (Mult Var Var)) i"
value "reduc_exp(Add(Mult (Add (Const 2) Var) (Add (Mult Var Var)(Const 3))) (Mult Var Var)) []"

fun pick :: "(int*int)list \<Rightarrow> nat \<Rightarrow> int list" where
"pick [] index = []" | 
"pick ((c,p)#t) index = (if (p = (int(index))) then c # (pick t (Suc index))
                         else 0 # (pick ((c,p)#t)(Suc index)))"
fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs e = pick(reduc_exp e []) 0"*)


fun add_helper :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_helper [] x = x" |
"add_helper x [] = x" |
"add_helper (h1#t1) (h2#t2) = (h1 + h2) # (add_helper t1 t2)"


fun mult_single :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"mult_single a [] = []" |
"mult_single a (h#t) = (a*h)# mult_single a t"

fun mult_helper :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_helper l1 [] = []"|
"mult_helper l1 (h2#t2) = add_helper (mult_single h2 l1) (mult_helper (0#l1) t2) "

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0,1]" |
"coeffs (Const n) = [n]" |
"coeffs (Add x y) = add_helper (coeffs x) (coeffs y)" |
"coeffs (Mult x y) = mult_helper (coeffs x) (coeffs y)"
value "eval(Add(Mult (Add (Const 2) Var) (Add (Mult Var Var)(Const 3))) (Mult Var Var)) i"
value "coeffs (Add(Mult (Add (Const 2) Var) (Add (Mult Var Var)(Const 3))) (Mult Var Var))"
value "coeffs (Add(Add (Add(Const 2) Var) (Add (Mult Var Var)(Const 3))) (Mult Var Var))"
value "eval (Add(Add (Add(Const 2) Var) (Add (Mult Var Var)(Const 3))) (Mult Var Var)) i"
text{*
Prove that @{text coeffs} preserves the value of the expression:
*}

lemma add_helper_evalp [simp] : "evalp0 (add_helper l1 l2) n  x = evalp0 l1 n  x + evalp0 l2 n x"
apply (induction l1 l2 arbitrary: n rule: add_helper.induct)
apply (auto  simp add : algebra_simps)
done

lemma mult_single_evalp [simp] : "evalp0 (mult_single h l) n x = h* (evalp0 l n x)"
apply (induction l arbitrary:n rule:mult_single.induct)
apply (auto  simp add : algebra_simps)
done


lemma evalp0_Suc [simp]: "evalp0 l (Suc n) x = x *(evalp0 l n x)"
apply (induction l arbitrary: n x)
apply (auto simp add : algebra_simps)
done
lemma mult_helper_evalp [simp]: "evalp0 (mult_helper l1 l2) 0 x = (evalp0 l1 0 x) * (evalp0 l2 0 x) "
apply (induction l2 arbitrary: l1 x)
apply (auto  simp add : algebra_simps)
done

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
apply (induct  e rule: coeffs.induct)
apply (auto  simp add : algebra_simps)
done
text{*
Hint: consider the hint in Exercise~\ref{exe:tree0}.
\endexercise
*}

end

