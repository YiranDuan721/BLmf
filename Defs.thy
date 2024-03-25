theory Defs
  imports "HOL-Algebra.Lattice"
begin

(* Cited paper:
Cantone, D., Zarba, C.G. (2006). A Decision Procedure for Monotone Functions over Bounded and Complete Lattices. In: de Swart, H., Orłowska, E., Schmidt, G., Roubens, M. (eds) Theory and Applications of Relational Structures as Knowledge Instruments II. Lecture Notes in Computer Science(), vol 4342. Springer, Berlin, Heidelberg.
https://doi.org/10.1007/11964810_15
*)

section \<open>Syntax of BLmf\<close>
(* Based on Definition 17, Section 2.4 of the cited paper *)

datatype BLmf_func = F string (* Unary functions *)

datatype BLmf_term =
    V string
  | Const1 (".1")
  | Const0 (".0")
  | Meet BLmf_term BLmf_term  (infix ".\<sqinter>" 66)
  | Join BLmf_term BLmf_term  (infix ".\<squnion>" 65)
  | FuncApp BLmf_func BLmf_term ("._ _")

(* BLmf_atoms are predicates on BLmf_terms *)
datatype BLmf_atom =
    Equals BLmf_term BLmf_term (infix "\<doteq>" 50)
  | LessEq BLmf_term BLmf_term (infix ".\<le>" 50)
  | Inc BLmf_func ("inc'(_')" [60] 60)
  | Dec BLmf_func ("dec'(_')" [60] 60)
  | ConstF BLmf_func ("const'(_')" [60] 60)
  | LeqF BLmf_func BLmf_func ("leq'(_, _')" [60, 61] 60)


section \<open>Semantics of BLmf\<close>
(* Based on Definition 18, Section 2.5 of the cited paper *)

type_synonym 'a BLmf_var_state = "string \<Rightarrow> 'a"
type_synonym 'a BLmf_fun_state = "string \<Rightarrow> ('a \<Rightarrow> 'a)"

fun eval_term :: "BLmf_term \<Rightarrow> 'a gorder \<Rightarrow> 'a BLmf_var_state \<Rightarrow> 'a BLmf_fun_state \<Rightarrow> 'a" where
  "eval_term      (V x) _ var_st      _ = var_st x"
| "eval_term         .1 L      _      _ = \<top>\<^bsub>L\<^esub>" (* The top element *)
| "eval_term         .0 L      _      _ = \<bottom>\<^bsub>L\<^esub>" (* The bottom element *)
| "eval_term (t1 .\<sqinter> t2) L var_st fun_st = (eval_term t1 L var_st fun_st) \<sqinter>\<^bsub>L\<^esub> (eval_term t2 L var_st fun_st)" (* Meet *)
| "eval_term (t1 .\<squnion> t2) L var_st fun_st = (eval_term t1 L var_st fun_st) \<squnion>\<^bsub>L\<^esub> (eval_term t2 L var_st fun_st)" (* Join *)
| "eval_term (.(F f) t) L var_st fun_st = (fun_st f) (eval_term t L var_st fun_st)" (* The evaluation of unary functions *)

fun eval_atom :: "BLmf_atom \<Rightarrow> 'a gorder \<Rightarrow> 'a BLmf_var_state \<Rightarrow> 'a BLmf_fun_state \<Rightarrow> bool" where
  "eval_atom (t1 \<doteq> t2) L var_st fun_st = ((eval_term t1 L var_st fun_st) .=\<^bsub>L\<^esub> (eval_term t2 L var_st fun_st))"
| "eval_atom (t1 .\<le> t2) L var_st fun_st = ((eval_term t1 L var_st fun_st) \<sqsubseteq>\<^bsub>L\<^esub> (eval_term t2 L var_st fun_st))"
(* inc(F f): The function f is monotone increasing *)
| "eval_atom (inc(F f)) L var_st fun_st =
  (\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longrightarrow> (fun_st f) x \<sqsubseteq>\<^bsub>L\<^esub> (fun_st f) y)"
(* dec(F f): The function f is monotone decreasing *)
| "eval_atom (dec(F f)) L var_st fun_st =
  (\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longrightarrow> (fun_st f) y \<sqsubseteq>\<^bsub>L\<^esub> (fun_st f) x)"
(* const(F f): The function f is constant *)
| "eval_atom (const(F f)) L var_st fun_st =
  (\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<longrightarrow> (fun_st f) x .=\<^bsub>L\<^esub> (fun_st f) y)"
(* leq(F f, F g): The output of f is always less than or equal to the output of g, for the same input.*)
| "eval_atom (leq(F f, F g)) L var_st fun_st = (let ff = fun_st f in let gg = fun_st g in
  \<forall>x. x \<in> carrier L \<longrightarrow> ff x \<sqsubseteq>\<^bsub>L\<^esub> gg x)"

(* In a valid evaluation "eval_atom Atom L var_st fun_st", the parameters must satisfy the following conditions:
1. L is a bounded lattice
2. every variable name is mapped to a member of the carrier set of L
3. every function name is mapped to a valid function, i.e. function that maps the carrier set of L to a subset of it *)
definition eval_atom_valid :: "'a gorder \<Rightarrow> 'a BLmf_var_state \<Rightarrow> 'a BLmf_fun_state \<Rightarrow> bool" where
 "eval_atom_valid L var_st fun_st \<longleftrightarrow>
  (bounded_lattice L) \<and>
  (\<forall>x. var_st x \<in> carrier L) \<and>
  (\<forall>f x. x \<in> carrier L \<longrightarrow> (fun_st f) x \<in> carrier L)"


section \<open>Substitution functions\<close>
(* Using the following function, all occurrence of
   a variable or constant in a term or atom can be replaced with another variable or constant.*)

(* substitute one variable with another variable in a term *)
fun subst_vv_term :: "BLmf_term \<Rightarrow> string \<Rightarrow> string \<Rightarrow> BLmf_term" where
  "subst_vv_term (V a) x y = (if (a = x) then (V y) else (V a))"
| "subst_vv_term (t\<^sub>1 .\<sqinter> t\<^sub>2) x y = (subst_vv_term t\<^sub>1 x y) .\<sqinter> (subst_vv_term t\<^sub>2 x y)"
| "subst_vv_term (t\<^sub>1 .\<squnion> t\<^sub>2) x y = (subst_vv_term t\<^sub>1 x y) .\<squnion> (subst_vv_term t\<^sub>2 x y)"
| "subst_vv_term (.f t) x y = .f (subst_vv_term t x y)"
| "subst_vv_term const x y = const"

(* substitute one variable with another variable in an atom *)
fun subst_vv :: "BLmf_atom \<Rightarrow> string \<Rightarrow> string \<Rightarrow> BLmf_atom" where
  "subst_vv (t\<^sub>1 \<doteq> t\<^sub>2) x y = ((subst_vv_term t\<^sub>1 x y) \<doteq> (subst_vv_term t\<^sub>2 x y))"
| "subst_vv (t\<^sub>1 .\<le> t\<^sub>2) x y = ((subst_vv_term t\<^sub>1 x y) .\<le> (subst_vv_term t\<^sub>2 x y))"
| "subst_vv func_atom x y = func_atom"

(* substitute one variable with the constant 1 in a term *)
fun subst_v1_term :: "BLmf_term \<Rightarrow> string \<Rightarrow> BLmf_term" where
  "subst_v1_term (V a) x = (if (a = x) then .1 else (V a))"
| "subst_v1_term (t\<^sub>1 .\<sqinter> t\<^sub>2) x = (subst_v1_term t\<^sub>1 x) .\<sqinter> (subst_v1_term t\<^sub>2 x)"
| "subst_v1_term (t\<^sub>1 .\<squnion> t\<^sub>2) x = (subst_v1_term t\<^sub>1 x) .\<squnion> (subst_v1_term t\<^sub>2 x)"
| "subst_v1_term (.f t) x = .f (subst_v1_term t x)"
| "subst_v1_term const x = const"

(* substitute one variable with the constant 1 in an atom *)
fun subst_v1 :: "BLmf_atom \<Rightarrow> string \<Rightarrow> BLmf_atom" where
  "subst_v1 (t\<^sub>1 \<doteq> t\<^sub>2) x = ((subst_v1_term t\<^sub>1 x) \<doteq> (subst_v1_term t\<^sub>2 x))"
| "subst_v1 (t\<^sub>1 .\<le> t\<^sub>2) x = ((subst_v1_term t\<^sub>1 x) .\<le> (subst_v1_term t\<^sub>2 x))"
| "subst_v1 func_atom x = func_atom"

(* substitute the constant 1 with one variable in a term *)
fun subst_1v_term :: "BLmf_term \<Rightarrow> string \<Rightarrow> BLmf_term" where
  "subst_1v_term (t\<^sub>1 .\<sqinter> t\<^sub>2) x = (subst_1v_term t\<^sub>1 x) .\<sqinter> (subst_1v_term t\<^sub>2 x)"
| "subst_1v_term (t\<^sub>1 .\<squnion> t\<^sub>2) x = (subst_1v_term t\<^sub>1 x) .\<squnion> (subst_1v_term t\<^sub>2 x)"
| "subst_1v_term (.f t) x = .f (subst_1v_term t x)"
| "subst_1v_term .1 x = (V x)"
| "subst_1v_term v_or_0 x = v_or_0"

(* substitute the constant 1 with one variable in an atom *)
fun subst_1v :: "BLmf_atom \<Rightarrow> string \<Rightarrow> BLmf_atom" where
  "subst_1v (t\<^sub>1 \<doteq> t\<^sub>2) x = ((subst_1v_term t\<^sub>1 x) \<doteq> (subst_1v_term t\<^sub>2 x))"
| "subst_1v (t\<^sub>1 .\<le> t\<^sub>2) x = ((subst_1v_term t\<^sub>1 x) .\<le> (subst_1v_term t\<^sub>2 x))"
| "subst_1v func_atom x = func_atom"

(* substitute one variable with the constant 0 in a term *)
fun subst_v0_term :: "BLmf_term \<Rightarrow> string \<Rightarrow> BLmf_term" where
  "subst_v0_term (V a) x = (if (a = x) then .0 else (V a))"
| "subst_v0_term (t\<^sub>1 .\<sqinter> t\<^sub>2) x = (subst_v0_term t\<^sub>1 x) .\<sqinter> (subst_v0_term t\<^sub>2 x)"
| "subst_v0_term (t\<^sub>1 .\<squnion> t\<^sub>2) x = (subst_v0_term t\<^sub>1 x) .\<squnion> (subst_v0_term t\<^sub>2 x)"
| "subst_v0_term (.f t) x = .f (subst_v0_term t x)"
| "subst_v0_term const x = const"

(* substitute one variable with the constant 0 in an atom *)
fun subst_v0 :: "BLmf_atom \<Rightarrow> string \<Rightarrow> BLmf_atom" where
  "subst_v0 (t\<^sub>1 \<doteq> t\<^sub>2) x = ((subst_v0_term t\<^sub>1 x) \<doteq> (subst_v0_term t\<^sub>2 x))"
| "subst_v0 (t\<^sub>1 .\<le> t\<^sub>2) x = ((subst_v0_term t\<^sub>1 x) .\<le> (subst_v0_term t\<^sub>2 x))"
| "subst_v0 func_atom x = func_atom"

(* substitute the constant 0 with one variable in a term *)
fun subst_0v_term :: "BLmf_term \<Rightarrow> string \<Rightarrow> BLmf_term" where
  "subst_0v_term (t\<^sub>1 .\<sqinter> t\<^sub>2) x = (subst_0v_term t\<^sub>1 x) .\<sqinter> (subst_0v_term t\<^sub>2 x)"
| "subst_0v_term (t\<^sub>1 .\<squnion> t\<^sub>2) x = (subst_0v_term t\<^sub>1 x) .\<squnion> (subst_0v_term t\<^sub>2 x)"
| "subst_0v_term (.f t) x = .f (subst_0v_term t x)"
| "subst_0v_term .0 x = (V x)"
| "subst_0v_term v_or_1 x = v_or_1"

(* substitute the constant 0 with one variable in an atom *)
fun subst_0v :: "BLmf_atom \<Rightarrow> string \<Rightarrow> BLmf_atom" where
  "subst_0v (t\<^sub>1 \<doteq> t\<^sub>2) x = ((subst_0v_term t\<^sub>1 x) \<doteq> (subst_0v_term t\<^sub>2 x))"
| "subst_0v (t\<^sub>1 .\<le> t\<^sub>2) x = ((subst_0v_term t\<^sub>1 x) .\<le> (subst_0v_term t\<^sub>2 x))"
| "subst_0v func_atom x = func_atom"

end