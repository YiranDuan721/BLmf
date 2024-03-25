theory Example
  imports Defs HelperLemmata BLmfRules
begin

(*
This is a formalization of Example 25 from the referenced paper:
Cantone, D., Zarba, C.G. (2006). A Decision Procedure for Monotone Functions over Bounded and Complete Lattices. In: de Swart, H., Orłowska, E., Schmidt, G., Roubens, M. (eds) Theory and Applications of Relational Structures as Knowledge Instruments II. Lecture Notes in Computer Science(), vol 4342. Springer, Berlin, Heidelberg.
https://doi.org/10.1007/11964810_15

The proof process is entirely consistent with the steps in the paper,
except that it skips the process of normalizing the set of literals.
*)

lemma example:
  assumes
    "eval_atom_valid L var_st fun_st"
    "distinct [a, y\<^sub>1, y\<^sub>2, z\<^sub>1, z\<^sub>2]"
    "eval_atom (.0 \<doteq> V a) L var_st fun_st"
    "eval_atom (inc(F f)) L var_st fun_st"
    "eval_atom (dec(F g)) L var_st fun_st"
    "eval_atom (leq(F f, F g)) L var_st fun_st"
    "eval_atom (V y\<^sub>1 \<doteq> .(F f)(V a)) L var_st fun_st"
    "eval_atom (V y\<^sub>2 \<doteq> .(F g)(V a)) L var_st fun_st"
    "eval_atom (V y\<^sub>1 \<doteq> V y\<^sub>2) L var_st fun_st"
    "eval_atom (V z\<^sub>1 \<doteq> .(F f)(V x)) L var_st fun_st"
    "eval_atom (V z\<^sub>2 \<doteq> .(F g)(V x)) L var_st fun_st"
    "\<not>eval_atom (V z\<^sub>1 \<doteq> V z\<^sub>2) L var_st fun_st"
  shows False
proof -
  have "eval_atom (.0 .\<le> V x) L var_st fun_st"
    using assms(1)
    by (rule le5)
  then have "eval_atom (V a .\<le> V x) L var_st fun_st"
    using assms(1, 3) eq2_0v
    by fastforce

  have "eval_atom (V y\<^sub>1 .\<le> V z\<^sub>1) L var_st fun_st"
    using
      \<open>eval_atom_valid L var_st fun_st\<close>
      \<open>eval_atom (inc(F f)) L var_st fun_st\<close>
      \<open>eval_atom (V a .\<le> V x) L var_st fun_st\<close>
      \<open>eval_atom (V y\<^sub>1 \<doteq> .(F f)(V a)) L var_st fun_st\<close>
      \<open>eval_atom (V z\<^sub>1 \<doteq> .(F f)(V x)) L var_st fun_st\<close>
    using func2 by blast

  have "eval_atom (V z\<^sub>1 .\<le> V z\<^sub>2) L var_st fun_st"
    using
      \<open>eval_atom_valid L var_st fun_st\<close>
      \<open>eval_atom (leq(F f, F g)) L var_st fun_st\<close>
      \<open>eval_atom (V z\<^sub>1 \<doteq> .(F f)(V x)) L var_st fun_st\<close>
      \<open>eval_atom (V z\<^sub>2 \<doteq> .(F g)(V x)) L var_st fun_st\<close>
    using func5 by blast

  have "eval_atom (V z\<^sub>2 .\<le> V y\<^sub>2) L var_st fun_st"
    using
      \<open>eval_atom_valid L var_st fun_st\<close>
      \<open>eval_atom (dec(F g)) L var_st fun_st\<close>
      \<open>eval_atom (V a .\<le> V x) L var_st fun_st\<close>
      \<open>eval_atom (V z\<^sub>2 \<doteq> .(F g)(V x)) L var_st fun_st\<close>
      \<open>eval_atom (V y\<^sub>2 \<doteq> .(F g)(V a)) L var_st fun_st\<close>
    using func3 by blast

  have "eval_atom (V z\<^sub>2 .\<le> V y\<^sub>1) L var_st fun_st"
  proof -
    have "z\<^sub>2 \<noteq> y\<^sub>2"
      using assms(2) by fastforce
    then have "subst_vv (V z\<^sub>2 .\<le> V y\<^sub>2) y\<^sub>2 y\<^sub>1 = (V z\<^sub>2 .\<le> V y\<^sub>1)"
      unfolding subst_vv.simps(2)
      unfolding subst_vv_term.simps(1)
      by simp
    then show "eval_atom (V z\<^sub>2 .\<le> V y\<^sub>1) L var_st fun_st"
      using
        \<open>eval_atom_valid L var_st fun_st\<close>
        \<open>eval_atom (V y\<^sub>1 \<doteq> V y\<^sub>2) L var_st fun_st\<close>
        \<open>eval_atom (V z\<^sub>2 .\<le> V y\<^sub>2) L var_st fun_st\<close>
      using eq2_vv_right by metis
  qed

  have "eval_atom (V y\<^sub>1 .\<le> V z\<^sub>2) L var_st fun_st"
    using
      \<open>eval_atom_valid L var_st fun_st\<close>
      \<open>eval_atom (V y\<^sub>1 .\<le> V z\<^sub>1) L var_st fun_st\<close>
      \<open>eval_atom (V z\<^sub>1 .\<le> V z\<^sub>2) L var_st fun_st\<close>
    using le3 by blast

  have "eval_atom (V z\<^sub>2 \<doteq> V y\<^sub>1) L var_st fun_st"
    using
      \<open>eval_atom_valid L var_st fun_st\<close>
      \<open>eval_atom (V y\<^sub>1 .\<le> V z\<^sub>2) L var_st fun_st\<close>
      \<open>eval_atom (V z\<^sub>2 .\<le> V y\<^sub>1) L var_st fun_st\<close>
    using le2 by blast

  have "eval_atom (V z\<^sub>1 .\<le> V y\<^sub>1) L var_st fun_st"
  proof -
    have "z\<^sub>1 \<noteq> z\<^sub>2"
      using assms(2) by fastforce
    then have "subst_vv (V z\<^sub>1 .\<le> V z\<^sub>2) z\<^sub>2 y\<^sub>1 = (V z\<^sub>1 .\<le> V y\<^sub>1)"
      unfolding subst_vv.simps(2)
      unfolding subst_vv_term.simps(1)
      by simp
    then show "eval_atom (V z\<^sub>1 .\<le> V y\<^sub>1) L var_st fun_st"
      using
        \<open>eval_atom_valid L var_st fun_st\<close>
        \<open>eval_atom (V z\<^sub>2 \<doteq> V y\<^sub>1) L var_st fun_st\<close>
        \<open>eval_atom (V z\<^sub>1 .\<le> V z\<^sub>2) L var_st fun_st\<close>
      using eq2_vv_left by metis
  qed

  have "eval_atom (V z\<^sub>1 \<doteq> V y\<^sub>1) L var_st fun_st"
    using
      \<open>eval_atom_valid L var_st fun_st\<close>
      \<open>eval_atom (V y\<^sub>1 .\<le> V z\<^sub>1) L var_st fun_st\<close>
      \<open>eval_atom (V z\<^sub>1 .\<le> V y\<^sub>1) L var_st fun_st\<close>
    using le2 by blast

  have "eval_atom (V z\<^sub>1 \<doteq> V z\<^sub>2) L var_st fun_st"
  proof -
    have "z\<^sub>1 \<noteq> y\<^sub>1"
      using assms(2) by fastforce
    then have "subst_vv (V z\<^sub>1 \<doteq> V y\<^sub>1) y\<^sub>1 z\<^sub>2 = (V z\<^sub>1 \<doteq> V z\<^sub>2)"
      unfolding subst_vv.simps(1)
      unfolding subst_vv_term.simps(1)
      by simp
    then show "eval_atom (V z\<^sub>1 \<doteq> V z\<^sub>2) L var_st fun_st"
      using
        \<open>eval_atom_valid L var_st fun_st\<close>
        \<open>eval_atom (V z\<^sub>1 \<doteq> V y\<^sub>1) L var_st fun_st\<close>
        \<open>eval_atom (V z\<^sub>2 \<doteq> V y\<^sub>1) L var_st fun_st\<close>
      using eq2_vv_right by metis
  qed

  show False
    using 
      \<open>eval_atom (V z\<^sub>1 \<doteq> V z\<^sub>2) L var_st fun_st\<close>
      \<open>\<not>eval_atom (V z\<^sub>1 \<doteq> V z\<^sub>2) L var_st fun_st\<close>
    by simp
qed

end