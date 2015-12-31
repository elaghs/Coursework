(* Elaheh Ghassabani, University of Minnesota, Summer2015 *)
theory Chapter3
imports "~~/src/HOL/IMP/BExp"
        "~~/src/HOL/IMP/ASM"
begin


fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (Plus (N n) (N m)) = False" |
"optimal (Plus a b) = conj (optimal a) (optimal b)" |
"optimal _ = True"


lemma "optimal (asimp_const a)"
apply (induction a)
apply (auto split: aexp.split)
done


fun sumN :: "aexp \<Rightarrow> int" where
"sumN (N n) = n" |
"sumN (V x) = 0" |
"sumN (Plus a b) = sumN a + sumN b"

value "sumN(Plus (Plus(V a) (Plus (N 4) (N 1))) (N 6))"

fun zeroN :: "aexp \<Rightarrow> aexp" where
"zeroN (N n) = N 0" |
"zeroN (V x) = V x" |
"zeroN (Plus a b) = Plus (zeroN a) (zeroN b)"
value "zeroN(Plus (Plus(V a) (Plus (N 4) (N 1))) (N 6))"


(* how to write \<lambda>? got it :D  \< lambda >*)
value "aval (Plus (N 3) (V ''x'')) (\<lambda>x.0) "
definition sepN :: "aexp \<Rightarrow> aexp" where
"sepN e = Plus (N (sumN e)) (zeroN e) "
value "sumN (N 2)"
value "zeroN (N 2)"
value "sepN (N 2)"

lemma aval_sepN [simp]: "aval (sepN t) s = aval t s"
apply (induction t)
apply(auto simp add:sepN_def)
done


definition full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp e = asimp (sepN e)"

lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
apply (induction t)
apply (auto simp add:full_asimp_def)
done

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x  _ (N n) = N n" |
"subst x a (V y) = (if (x = y) then a else V y)" |
"subst x e (Plus a b) = Plus (subst x e a)(subst x e b)" 
(*I don't get why when use ''x'' instead of x it goes crazy!! *)

value "subst ''x'' (Plus (V ''x'')(N 3)) (Plus (N 4) (Plus (Plus (N 2) (Plus (V ''x'')(V y)))(V ''x'')))"


lemma  "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')"
apply simp
done
lemma subst_lemma [simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
apply (induction e arbitrary:a)
apply (auto)
done

 
lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
apply (induction a1 arbitrary: a2)
apply (auto simp add:subst_lemma)
done

text{*
\endexercise

\exercise
Take a copy of theory @{theory AExp} and modify it as follows.
Extend type @{typ aexp} with a binary constructor @{text Times} that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const asimp_const}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
*}
(* done! in a seperate file: AExp2 *)


datatype aexp2 = N' int | V' vname | Plus' aexp2 aexp2 | Inc vname | Div aexp2 aexp2
(**********************************************************)
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow>  (val \<times> state) option" where
"aval2 (N' n) s = Some (n, s)" |
"aval2 (V' x) s = Some (s x, s)" |
"aval2 (Inc x) s = Some ((s x) + 1, s (x := ((s x)+1)))" |
"aval2 (Plus' a\<^sub>1 a\<^sub>2) s =(case (aval2 a\<^sub>1 s) of
                         Some (a, s') \<Rightarrow> (case (aval2 a\<^sub>2 s')  of 
                                    Some (b, s'') \<Rightarrow> Some(a + b, s'')|
                                    None   \<Rightarrow> None) |
                         None  \<Rightarrow> None)" |
"aval2 (Div a\<^sub>1 a\<^sub>2) s = (case (aval2 a\<^sub>1 s) of 
                        None \<Rightarrow> None |
                        Some (a, s') \<Rightarrow> (case (aval2 a\<^sub>2 s') of
                                          None \<Rightarrow> None |
                                          Some (b, s'') \<Rightarrow> 
                                          (if(b = 0) then None else Some (a div b, s''))))"
text{*
\endexercise

\exercise
The following type adds a @{text LET} construct to arithmetic expressions:
*}

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp
fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl c) s = c" |
"lval (Vl x) s = s x" | 
"lval (Plusl a b) s = (lval a s) + (lval b s)" |
"lval (LET x a b) s = lval b (s(x := lval a s))"


fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl c) = N c" |
"inline (Vl x) = V x" | 
"inline (Plusl a b) = Plus (inline a) (inline b)" |
"inline (LET x a b) = subst x (inline a) (inline b)"

lemma leval_aval: "lval e s = aval (inline e) s"
apply (induction e arbitrary:s rule: inline.induct)
apply (auto)
done

text{* The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of @{text e\<^sub>2}
in the state where @{text x} is bound to the value of @{text e\<^sub>1} in the original state.
Define a function @{const lval} @{text"::"} @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{const inline} @{text"::"} @{typ "lexp \<Rightarrow> aexp"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of @{text e\<^sub>1} for @{text x} in the converted form of @{text e\<^sub>2}.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{const inline} is correct w.r.t.\ evaluation.
\endexercise


\exercise
Show that equality and less-or-equal tests on @{text aexp} are definable
*}



definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a b = Not (Less b a) "

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a b = And (Not(Less a b)) (Not(Less b a))"

text{*
and prove that they do what they are supposed to:
*}

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
apply (auto simp add:  Le_def)
done

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
apply (auto simp add:  Eq_def)
done

text{*
\endexercise

\exercise
Consider an alternative type of boolean expressions featuring a conditional: *}

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

text {*  First define an evaluation function analogously to @{const bval}: *}

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b) s = b"|
"ifval (Less2 a b) s = (aval a s < aval b s)" |
"ifval (If c t e) s = (if (ifval c s) then (ifval t s) else (ifval e s))"

text{* Then define two translation functions *}

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v) = Bc2 v" |
"b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
"b2ifexp (And b1 b2) = If (b2ifexp b1) (If (b2ifexp b2) (Bc2 True)(Bc2 False)) (Bc2 False)" |
"b2ifexp (Less a1 a2) = Less2 a1 a2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v) = Bc v" | 
"if2bexp (Less2 a1 a2) = Less a1 a2" |
"if2bexp (If c t e) = Not (And (Not (And (if2bexp c) (if2bexp t)))(Not (And (Not (if2bexp c))(if2bexp e))))"

text{* and prove their correctness: *}

lemma "bval (if2bexp exp) s = ifval exp s"
apply (induction exp arbitrary:s)
apply (auto)
done

lemma "ifval (b2ifexp exp) s = bval exp s"
apply (induction exp arbitrary:s)
apply (auto)
done

text{*
\endexercise

\exercise
We define a new type of purely boolean expressions without any arithmetic
*}

datatype pbexp =
  VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

text{*
where variables range over values of type @{typ bool},
as can be seen from the evaluation function:
*}

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"  |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)" 

text {* Define a function that checks whether a boolean exression is in NNF
(negation normal form), i.e., if @{const NOT} is only applied directly
to @{const VAR}s: *}

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
(* "is_nnf (NOT b) = (case b of 
                    (VAR x) \<Rightarrow> True |
                      _     \<Rightarrow> False) " | *)
"is_nnf (NOT (VAR x)) = True" |
"is_nnf (NOT b) = False" | 
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2) " |
"is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2) "



text{*
Now define a function that converts a @{text bexp} into NNF by pushing
@{const NOT} inwards as much as possible:
*}

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = VAR x"  |
"nnf (NOT (VAR x)) = NOT (VAR x)" |
"nnf (NOT (NOT b)) = nnf b " |
"nnf (AND b1 b2) = AND (nnf b1) (nnf b2)" |
"nnf (OR b1 b2)  = OR (nnf b1) (nnf b2)"| 
"nnf (NOT (AND b1 b2)) = OR (nnf (NOT b1)) (nnf (NOT b2))" |
"nnf (NOT (OR b1 b2))  = AND (nnf (NOT b1)) (nnf (NOT b2))" 

text{*
Prove that @{const nnf} does what it is supposed to do:
*}

lemma pbval_nnf [simp]: "pbval (nnf b) s = pbval b s"
apply (induction b arbitrary:s rule: nnf.induct)
apply (auto)
done

lemma is_nnf_nnf [simp]: "is_nnf (nnf b)"
apply (induction b rule: nnf.induct)
apply (auto)
done

text{*
An expression is in DNF (disjunctive normal form) if it is in NNF
and if no @{const OR} occurs below an @{const AND}. Define a corresponding
test:
*}

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
"is_dnf (NOT (VAR x)) = True" |
"is_dnf (NOT b) = False" | 
(* "is_dnf (NOT b) = (case b of 
                    (VAR x) \<Rightarrow> True |
                      _     \<Rightarrow> False) " | *)
"is_dnf (AND (OR x y) b2) =  False " |
"is_dnf (AND b1 (OR x y)) =  False " |
"is_dnf (AND b1 b2) =  (is_dnf b1 \<and> is_dnf b2) " |
"is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2) "
value "is_dnf (OR (NOT (OR (VAR x)(VAR y)))(AND (VAR x) (NOT (VAR y))))"
value "is_dnf (OR (OR (OR (VAR x)(VAR y)) (NOT (VAR x)))(AND (VAR x) (NOT (VAR y))))"
value "is_dnf (AND (VAR x) (VAR y))"
text {*
An NNF can be converted into a DNF in a bottom-up manner.
The critical case is the conversion of @{term (sub) "AND b1 b2"}.
Having converted @{text b\<^sub>1} and @{text b\<^sub>2}, apply distributivity of @{const AND}
over @{const OR}. If we write @{const OR} as a multi-argument function,
we can express the distributivity step as follows:
@{text "dist_AND (OR a\<^sub>1 ... a\<^sub>n) (OR b\<^sub>1 ... b\<^sub>m)"}
= @{text "OR (AND a\<^sub>1 b\<^sub>1) (AND a\<^sub>1 b\<^sub>2) ... (AND a\<^sub>n b\<^sub>m)"}. Define
*}
 

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
  "dist_AND (OR a b) c = (OR (dist_AND a c) (dist_AND b c))" | 
  "dist_AND a (OR b c) = (OR (dist_AND a b) (dist_AND a c))" |
  "dist_AND a b = (AND a b)"

value"dist_AND (OR (VAR x) (VAR y)) (NOT(VAR b))"
value"dist_AND (AND (VAR x) (VAR y)) (OR (VAR a)(VAR b))"

text {* and prove that it behaves as follows: *}

lemma pbval_dist [simp]: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
apply (induction b1 b2 arbitrary: s rule: dist_AND.induct)
apply (auto)
done



lemma is_dnf_dist [simp]: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
apply (induction b1 b2 rule: dist_AND.induct)
apply (auto)
done

text {* Use @{const dist_AND} to write a function that converts an NNF
  to a DNF in the above bottom-up manner.
*}

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR b) = VAR b" |
"dnf_of_nnf (NOT b) = NOT b" |
"dnf_of_nnf (AND b1 b2) = dist_AND (dnf_of_nnf b1) (dnf_of_nnf b2)" |
"dnf_of_nnf (OR b11 b12) = OR (dnf_of_nnf b11) (dnf_of_nnf b12)"  


value "dnf_of_nnf (AND (OR (VAR x) (VAR y)) (NOT(VAR b)))"
value "dist_AND ((OR (VAR x) (VAR y))) ((AND (NOT(VAR b)) (OR (VAR c) (VAR d))))"
value "dnf_of_nnf (AND (OR (VAR x) (VAR y)) (AND (NOT(VAR b)) (OR (VAR c) (VAR d))))"
value"dnf_of_nnf (AND (AND (VAR x) (VAR y)) (OR (VAR a)(VAR b)))"
text {* Prove the correctness of your function: *}

lemma nnf_dist_AND [simp]: "is_nnf b1 \<Longrightarrow> is_nnf b2 \<Longrightarrow> is_nnf (dist_AND b1 b2)"
apply (induction b1 b2 rule: dist_AND.induct)
apply (auto)
done

(*lemma nnf_dnf_AND : "is_nnf (dist_AND b1 b2) \<Longrightarrow> is_dnf (dist_AND b1 b2)"
apply (induction b1 b2 rule: dist_AND.induct)
apply (auto)
*)
lemma "pbval (dnf_of_nnf b) s = pbval b s"
apply (induction b arbitrary: s rule:dnf_of_nnf.induct)
apply (auto)
done

 
lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
apply (induction b rule:is_nnf.induct)
apply (auto)
done



type_synonym reg = nat
datatype instrg = LDI val reg | LD vname reg | ADD reg reg

type_synonym rstate = "reg \<Rightarrow> val"

fun execr1 :: "instrg \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"execr1 (LDI i r) s rs =  rs(r := i)" |
"execr1 (LD x r) s rs = rs (r := s(x))"|
"execr1 (ADD r1 r2) s rs = rs (r1 := (rs (r1) + rs (r2)))"

fun execr :: "instrg list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"execr [] s rs = rs" |
"execr (h#t) s rs  = execr t s (execr1 h s rs)"

fun compr :: "aexp \<Rightarrow> reg \<Rightarrow> instrg list" where
"compr (N i) r = [LDI i r]" |
"compr (V x) r = [LD x r]" |
"compr (Plus a b) r =  (compr a r) @ (compr b (Suc r))@[ADD r (Suc r)] "

value "compr (Plus (Plus (V x) (N 8))(Plus (N 4) (V y))) 0 "
value "execr (compr (Plus (Plus (V ''x'') (N 8))(Plus (N 4) (V ''y''))) 0) <''x'' := 5, ''y'' := 3> <> 0 "


(*lemma exec_Nil[simp] :  "execr [] s rs = rs"
apply (auto)
done*)

(*lemma execr1_exec [simp] : "execr (h#t) s rs = execr t s (execr1 h s rs)"
apply (auto)
done
*)
lemma app_ex [simp]: "execr (is1 @ is2) s rs = execr is2 s (execr is1 s rs)"
apply(induction is1 arbitrary: rs)
apply(auto)
done
(*lemma compr_Nil [simp]: "[] = compr a r \<Longrightarrow> False" 
apply (induction rule:compr.induct)
apply (auto)
done*)
lemma reg_non_interference [simp] : "r < cr \<Longrightarrow> (execr (compr a cr) s rs r) = rs r"
apply (induction cr arbitrary: rs rule:compr.induct)
apply (auto)
done

theorem "execr (compr a r) s rs r = aval a s"
apply (induction a arbitrary:  r rs)
apply (auto)
done
text{*
\endexercise

\exercise\label{exe:accumulator}
This exercise is a variation of the previous one
with a different instruction set:
*}

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

text{*
All instructions refer implicitly to register 0 as a source or target:
@{const LDI0} and @{const LD0} load a value into register 0, @{term "MV0 r"}
copies the value in register 0 into register @{text r}, and @{term "ADD0 r"}
adds the value in register @{text r} to the value in register 0;
@{term "MV0 0"} and @{term "ADD0 0"} are legal. Define the execution functions
*}

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"exec01 (LDI0 i) s rs = rs (0 := i)" |
"exec01 (LD0 x) s rs = rs (0 := s(x))"|
"exec01 (MV0 r) s rs = rs (r := rs 0)" |
"exec01 (ADD0 r) s rs = rs (0 := (rs 0 + rs r))"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate " where
"exec0 [] s rs = rs" |
"exec0 (h#t) s rs = exec0 t s (exec01 h s rs)"

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (N i) r = [LDI0 i]" |
"comp0 (V x) r = [LD0 x]" |
"comp0 (Plus a b) r =  (if (r = 0) then
                              (comp0 a 1) @ [MV0 1] @(comp0 b (Suc 1))@ [ADD0 1]
                         else (comp0 a r) @ [MV0 r] @(comp0 b (Suc r))@ [ADD0 r]) "

value "comp0 (Plus (Plus (V x) (N 8))(Plus (N 4) (V y))) 0 "
value "exec0 (comp0 (Plus (Plus (V ''x'') (N 8))(Plus (N 4) (V ''y''))) 0) <''x'' := 5, ''y'' := 3> <> 0"
text{*
and @{const exec0} for instruction lists.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into register 0. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "\<le> r"} should be left alone
(with the exception of 0). Define the compiler and prove it correct:
*}
lemma app_ex0 [simp]: "exec0 (is1 @ is2) s rs = exec0 is2 s (exec0 is1 s rs)"
apply(induction is1 arbitrary: rs)
apply(auto)
done
lemma exec0_reg [simp] : " cr > r \<and> r > 0  \<Longrightarrow> exec0 (comp0 a cr) s rs r = rs r"
apply (induction cr  arbitrary:  rs rule:comp0.induct)
apply (auto)
done
theorem "exec0 (comp0 a r) s rs 0 = aval a s"
apply (induction a arbitrary: r rs)
apply (auto)
done

text{*
\endexercise
*}

end

