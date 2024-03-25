theory BLmfRules
  imports Defs HelperLemmata
begin
(* The proofs for most of the inference rules described in Fig.1, section 3 of the cited paper:
Cantone, D., Zarba, C.G. (2006). A Decision Procedure for Monotone Functions over Bounded and Complete Lattices. In: de Swart, H., Orłowska, E., Schmidt, G., Roubens, M. (eds) Theory and Applications of Relational Structures as Knowledge Instruments II. Lecture Notes in Computer Science(), vol 4342. Springer, Berlin, Heidelberg.
https://doi.org/10.1007/11964810_15 *)

section \<open>=-rules\<close>

lemma eq1:
  assumes
    "eval_atom_valid L var_st fun_st"
  shows
    "eval_atom (V x \<doteq> V x) L var_st fun_st"
  unfolding eval_atom.simps(1)
  using assms unfolding eval_atom_valid_def
  by (simp add:
      bounded_lattice.axioms(2)
      equivalence.refl
      weak_partial_order.axioms(1)
      weak_partial_order_bottom.axioms(1))

(* x = y, l \<Longrightarrow> l[x/y] *)
lemma eq2_vv_left:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x \<doteq> V y) L var_st fun_st"
    "eval_atom a L var_st fun_st"
  shows
    "eval_atom (subst_vv a x y) L var_st fun_st"
  using assms
proof (induction a)
  case (Equals x1 x2)
  then show ?case
    unfolding eval_atom_valid_def
    unfolding subst_vv.simps(1)
    by (metis Equals.prems(1) eq_symmetrical eq_transitive subst_vv_term_eq)
next
  case (LessEq x1 x2)
  moreover
  have "eval_atom (x1 \<doteq> (subst_vv_term x1 x y)) L var_st fun_st"
       "eval_atom (x2 \<doteq> (subst_vv_term x2 x y)) L var_st fun_st"
    using assms(1-2) subst_vv_term_eq
    by blast+
  ultimately
  show ?case
    unfolding eval_atom_valid_def
    unfolding eval_atom.simps(1-2)
    by (simp add:
        bounded_lattice.axioms(1) lattice.axioms(2) lower_semilattice.axioms(1)
        partial_order.eq_is_equal)
qed simp+

(* y = x, l \<Longrightarrow> l[x/y] *)
lemma eq2_vv_right:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V y \<doteq> V x) L var_st fun_st"
    "eval_atom a L var_st fun_st"
  shows
    "eval_atom (subst_vv a x y) L var_st fun_st"
  using assms
  using eq2_vv_left eq_symmetrical
  by blast
(* x = 0, l \<Longrightarrow> l[x/0] *)
lemma eq2_v0:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x \<doteq> .0) L var_st fun_st"
    "eval_atom a L var_st fun_st"
  shows
    "eval_atom (subst_v0 a x) L var_st fun_st"
  using assms
proof (induction a)
  case (Equals x1 x2)
  then show ?case
    unfolding eval_atom_valid_def
    unfolding subst_v0.simps(1)
    by (metis Equals.prems(1) eq_symmetrical eq_transitive subst_v0_term_eq)
next
  case (LessEq x1 x2)
  moreover
  have "eval_atom (x1 \<doteq> (subst_v0_term x1 x)) L var_st fun_st"
       "eval_atom (x2 \<doteq> (subst_v0_term x2 x)) L var_st fun_st"
    using assms(1-2) subst_v0_term_eq
    by blast+
  ultimately
  show ?case
    unfolding eval_atom_valid_def
    unfolding eval_atom.simps(1-2)
    by (simp add:
        bounded_lattice.axioms(1) lattice.axioms(2) lower_semilattice.axioms(1)
        partial_order.eq_is_equal)
qed simp+

(* 0 = x, l \<Longrightarrow> l[0/x] *)
lemma eq2_0v:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (.0 \<doteq> V x) L var_st fun_st"
    "eval_atom a L var_st fun_st"
  shows
    "eval_atom (subst_0v a x) L var_st fun_st"
  using assms
proof (induction a)
  case (Equals x1 x2)
  then show ?case
    unfolding eval_atom_valid_def
    unfolding subst_0v.simps(1)
    by (metis Equals.prems(1) eq_symmetrical eq_transitive subst_0v_term_eq)
next
  case (LessEq x1 x2)
  moreover
  have "eval_atom (x1 \<doteq> (subst_0v_term x1 x)) L var_st fun_st"
       "eval_atom (x2 \<doteq> (subst_0v_term x2 x)) L var_st fun_st"
    using assms(1-2) subst_0v_term_eq
    by blast+
  ultimately
  show ?case
    unfolding eval_atom_valid_def
    unfolding eval_atom.simps(1-2)
    by (simp add:
        bounded_lattice.axioms(1) lattice.axioms(2) lower_semilattice.axioms(1)
        partial_order.eq_is_equal)
qed simp+

(* x = 1, l \<Longrightarrow> l[x/1] *)
lemma eq2_v1:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x \<doteq> .1) L var_st fun_st"
    "eval_atom a L var_st fun_st"
  shows
    "eval_atom (subst_v1 a x) L var_st fun_st"
  using assms
proof (induction a)
  case (Equals x1 x2)
  then show ?case
    unfolding eval_atom_valid_def
    unfolding subst_v1.simps(1)
    by (metis Equals.prems(1) eq_symmetrical eq_transitive subst_v1_term_eq)
next
  case (LessEq x1 x2)
  moreover
  have "eval_atom (x1 \<doteq> (subst_v1_term x1 x)) L var_st fun_st"
       "eval_atom (x2 \<doteq> (subst_v1_term x2 x)) L var_st fun_st"
    using assms(1-2) subst_v1_term_eq
    by blast+
  ultimately
  show ?case
    unfolding eval_atom_valid_def
    unfolding eval_atom.simps(1-2)
    by (simp add:
        bounded_lattice.axioms(1) lattice.axioms(2) lower_semilattice.axioms(1)
        partial_order.eq_is_equal)
qed simp+

(* 1 = x, l \<Longrightarrow> l[1/x] *)
lemma eq2_1v:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (.1 \<doteq> V x) L var_st fun_st"
    "eval_atom a L var_st fun_st"
  shows
    "eval_atom (subst_1v a x) L var_st fun_st"
  using assms
proof (induction a)
  case (Equals x1 x2)
  then show ?case
    unfolding eval_atom_valid_def
    unfolding subst_1v.simps(1)
    by (metis Equals.prems(1) eq_symmetrical eq_transitive subst_1v_term_eq)
next
  case (LessEq x1 x2)
  moreover
  have "eval_atom (x1 \<doteq> (subst_1v_term x1 x)) L var_st fun_st"
       "eval_atom (x2 \<doteq> (subst_1v_term x2 x)) L var_st fun_st"
    using assms(1-2) subst_1v_term_eq
    by blast+
  ultimately
  show ?case
    unfolding eval_atom_valid_def
    unfolding eval_atom.simps(1-2)
    by (simp add:
        bounded_lattice.axioms(1) lattice.axioms(2) lower_semilattice.axioms(1)
        partial_order.eq_is_equal)
qed simp+


section \<open>\<le>-rules\<close>

(* Reflexivity *)
lemma le1:
  assumes
    "eval_atom_valid L var_st fun_st"
  shows "eval_atom (V x .\<le> V x) L var_st fun_st"
  unfolding eval_atom.simps(2)
  using assms unfolding eval_atom_valid_def
  by (simp add: bounded_lattice_def weak_partial_order.le_refl weak_partial_order_bottom.axioms(1))

(* Anti-reflexivity *)
lemma le2:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x .\<le> V y) L var_st fun_st"
    "eval_atom (V y .\<le> V x) L var_st fun_st"
  shows 
    "eval_atom (V x \<doteq> V y) L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  by (simp add: bounded_lattice.axioms(3) weak_partial_order.weak_le_antisym weak_partial_order_top.axioms(1))

(* Transitivity *)
lemma le3:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x .\<le> V y) L var_st fun_st"
    "eval_atom (V y .\<le> V z) L var_st fun_st"
  shows 
    "eval_atom (V x .\<le> V z) L var_st fun_st"
proof -
  let ?x = "var_st x"
  let ?y = "var_st y"
  let ?z = "var_st z"
  have "?x \<sqsubseteq>\<^bsub>L\<^esub> ?y" "?y \<sqsubseteq>\<^bsub>L\<^esub> ?z"
    using assms(2-3) unfolding eval_atom.simps(2) eval_term.simps(1)
    by simp+
  then have "?x \<sqsubseteq>\<^bsub>L\<^esub> ?z"
    using assms(1) unfolding eval_atom_valid_def
    by (meson bounded_lattice.axioms(3) weak_partial_order.le_trans weak_partial_order_top.axioms(1))
  then show "eval_atom (V x .\<le> V z) L var_st fun_st"
    unfolding eval_atom.simps(2) eval_term.simps(1)
    by simp
qed

(* Top element is the greatest *)
lemma le4:
  assumes "eval_atom_valid L var_st fun_st"
  shows 
    "eval_atom ((V x) .\<le> .1) L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  by (simp add: bounded_lattice.axioms(3) weak_partial_order_top.top_higher)

(* Bottom element is the least *)
lemma le5:
  assumes
    "eval_atom_valid L var_st fun_st"
  shows
    "eval_atom (.0 .\<le> V x) L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  by (simp add: bounded_lattice.axioms(2) weak_partial_order_bottom.bottom_lower)


section \<open>\<sqinter>-rules\<close>

(* x = y \<sqinter> z \<Longrightarrow> x \<le> y, x \<le> z *)
lemma meet1:
  assumes "eval_atom_valid L var_st fun_st"
          "eval_atom (V x \<doteq> V y .\<sqinter> V z) L var_st fun_st"
  shows "eval_atom (V x .\<le> V y) L var_st fun_st"
        "eval_atom (V x .\<le> V y) L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  by (simp add:
      bounded_lattice_def lattice_def lower_semilattice_axioms_def lower_semilattice_def
      partial_order.eq_is_equal weak_lower_semilattice.meet_left
      weak_lower_semilattice_axioms_def weak_lower_semilattice_def weak_partial_order_bottom_def)+

(* x = y \<sqinter> z, w \<le> y, w \<le> z \<Longrightarrow> w \<le> x *)
lemma meet2:
  assumes "eval_atom_valid L var_st fun_st"
          "eval_atom (V x \<doteq> V y .\<sqinter> V z) L var_st fun_st"
          "eval_atom (V w .\<le> V y) L var_st fun_st"
          "eval_atom (V w .\<le> V z) L var_st fun_st"
  shows 
          "eval_atom (V w .\<le> V x) L var_st fun_st"
proof -
  let ?x = "var_st x"
  let ?y = "var_st y"
  let ?z = "var_st z"
  let ?w = "var_st w"
  have "?x .=\<^bsub>L\<^esub> ?y \<sqinter>\<^bsub>L\<^esub> ?z"
       "?w \<sqsubseteq>\<^bsub>L\<^esub> ?y"
       "?w \<sqsubseteq>\<^bsub>L\<^esub> ?z"
    using assms unfolding eval_atom.simps eval_term.simps
    by blast+
  then have "?w \<sqsubseteq>\<^bsub>L\<^esub> ?x"
    using assms(1) unfolding eval_atom_valid_def
    by (simp add:
        bounded_lattice_def lattice_def lower_semilattice_axioms_def lower_semilattice_def
        partial_order.eq_is_equal weak_lower_semilattice.intro weak_lower_semilattice.meet_le
        weak_lower_semilattice_axioms_def weak_partial_order_bottom.axioms(1))
  then show "eval_atom (V w .\<le> V x) L var_st fun_st"
    unfolding eval_atom.simps eval_term.simps
    by blast
qed


section \<open>\<squnion>-rules\<close>

(* x = y \<squnion> z \<Longrightarrow> y \<le> x, z \<le> x *)
lemma join1:
  assumes "eval_atom_valid L var_st fun_st"
          "eval_atom (V x \<doteq> V y .\<squnion> V z) L var_st fun_st"
  shows "eval_atom (V y .\<le> V x) L var_st fun_st"
        "eval_atom (V z .\<le> V x) L var_st fun_st"
proof -
  let ?x = "var_st x"
  let ?y = "var_st y"
  let ?z = "var_st z"
  have "bounded_lattice L"
    using assms(1) unfolding eval_atom_valid_def by blast
  moreover
  have "?x \<in> carrier L" "?y \<in> carrier L" "?z \<in> carrier L"
    using assms(1) unfolding eval_atom_valid_def by blast+
  moreover
  have "?x .=\<^bsub>L\<^esub> ?y \<squnion>\<^bsub>L\<^esub> ?z"
    using assms(2) unfolding eval_atom.simps eval_term.simps by blast
  moreover
  have "weak_upper_semilattice L"
    using \<open>bounded_lattice L\<close>
    by (simp add:
        bounded_lattice.axioms(1) lattice.axioms(1) lattice.axioms(2)
        lower_semilattice.axioms(1) partial_order.axioms(1)
        upper_semilattice.sup_of_two_exists weak_upper_semilattice.intro
        weak_upper_semilattice_axioms.intro)
  moreover
  have "?y \<sqsubseteq>\<^bsub>L\<^esub> ?y \<squnion>\<^bsub>L\<^esub> ?z"
    using \<open>weak_upper_semilattice L\<close> \<open>?y \<in> carrier L\<close> \<open>?z \<in> carrier L\<close> weak_upper_semilattice.join_left
    by meson
  moreover
  have "?z \<sqsubseteq>\<^bsub>L\<^esub> ?y \<squnion>\<^bsub>L\<^esub> ?z"
    using \<open>weak_upper_semilattice L\<close> \<open>?y \<in> carrier L\<close> \<open>?z \<in> carrier L\<close> weak_upper_semilattice.join_right
    by meson
  ultimately
  have "?y \<sqsubseteq>\<^bsub>L\<^esub> ?x" "?z \<sqsubseteq>\<^bsub>L\<^esub> ?x"
    by (simp add: bounded_lattice_def lattice_def lower_semilattice_def partial_order.eq_is_equal)+
  then show "eval_atom (V y .\<le> V x) L var_st fun_st"
            "eval_atom (V z .\<le> V x) L var_st fun_st"
    unfolding eval_atom.simps eval_term.simps
    by blast+
qed

(* x = y \<squnion> z, y \<le> w, z \<le> w \<Longrightarrow> x \<le> w *)
lemma join2:
  assumes "eval_atom_valid L var_st fun_st"
          "eval_atom (V x \<doteq> V y .\<squnion> V z) L var_st fun_st"
          "eval_atom (V y .\<le> V w) L var_st fun_st"
          "eval_atom (V z .\<le> V w) L var_st fun_st"
  shows 
          "eval_atom (V x .\<le> V w) L var_st fun_st"
proof -
  let ?x = "var_st x"
  let ?y = "var_st y"
  let ?z = "var_st z"
  let ?w = "var_st w"
  have "?x .=\<^bsub>L\<^esub> ?y \<squnion>\<^bsub>L\<^esub> ?z"
       "?y \<sqsubseteq>\<^bsub>L\<^esub> ?w"
       "?z \<sqsubseteq>\<^bsub>L\<^esub> ?w"
    using assms unfolding eval_atom.simps eval_term.simps
    by blast+
  then have "?x \<sqsubseteq>\<^bsub>L\<^esub> ?w"
    using assms(1) unfolding eval_atom_valid_def
    by (metis (full_types)
        bounded_lattice_def lattice_def lower_semilattice_def
        partial_order.eq_is_equal
        upper_semilattice.axioms(2) upper_semilattice_axioms_def weak_partial_order_bottom.axioms(1)
        weak_upper_semilattice.intro weak_upper_semilattice_axioms.intro
        weak_upper_semilattice.join_le)  
  then show "eval_atom (V x .\<le> V w) L var_st fun_st"
    unfolding eval_atom.simps eval_term.simps
    by blast
qed


section \<open>Functions rules\<close>

(* x = x', y = f(x), y' = f(x') \<Longrightarrow> y = y' *)
lemma func1:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x \<doteq> V x') L var_st fun_st"
    "eval_atom (V y \<doteq> .(F f)(V x)) L var_st fun_st"
    "eval_atom (V y' \<doteq> .(F f)(V x')) L var_st fun_st"
  shows
    "eval_atom (V y \<doteq> V y') L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  by (simp add: bounded_lattice_def lattice_def lower_semilattice_def partial_order.eq_is_equal)

(* f monotone increases, x \<le> x', y = f(x), y' = f(x') \<Longrightarrow> y \<le> y' *)
lemma func2:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (inc(F f)) L var_st fun_st"
    "eval_atom (V x .\<le> V x') L var_st fun_st"
    "eval_atom (V y \<doteq> .(F f)(V x)) L var_st fun_st"
    "eval_atom (V y' \<doteq> .(F f)(V x')) L var_st fun_st"
  shows
    "eval_atom (V y .\<le> V y') L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  unfolding eval_term.simps
  by (meson bounded_lattice_def weak_partial_order.le_cong weak_partial_order_bottom_def)

(* f monotone decreases, x \<le> x', y = f(x), y' = f(x') \<Longrightarrow> y' \<le> y *)
lemma func3:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (dec(F f)) L var_st fun_st"
    "eval_atom (V x .\<le> V x') L var_st fun_st"
    "eval_atom (V y \<doteq> .(F f)(V x)) L var_st fun_st"
    "eval_atom (V y' \<doteq> .(F f)(V x')) L var_st fun_st"
  shows
    "eval_atom (V y' .\<le> V y) L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  unfolding eval_term.simps
  by (meson bounded_lattice_def weak_partial_order.le_cong weak_partial_order_bottom_def)

(* f is constant, y = f(x), y' = f(x') \<Longrightarrow> y = y' *)
lemma func4:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (const(F f)) L var_st fun_st"
    "eval_atom (V y \<doteq> .(F f)(V x)) L var_st fun_st"
    "eval_atom (V y' \<doteq> .(F f)(V x')) L var_st fun_st"
  shows
    "eval_atom (V y \<doteq> V y') L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  unfolding eval_term.simps
  by (meson
      bounded_lattice_def
      weak_partial_order.le_cong weak_partial_order.weak_le_antisym weak_partial_order.weak_refl
      weak_partial_order_top_def)

(* f(x) \<le> g(x) for all x, y = f(x), y' = g(x) \<Longrightarrow> y \<le> y' *)
lemma func5:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (leq(F f, F g)) L var_st fun_st"
    "eval_atom (V y \<doteq> .(F f)(V x)) L var_st fun_st"
    "eval_atom (V y' \<doteq> .(F g)(V x)) L var_st fun_st"
  shows
    "eval_atom (V y .\<le> V y') L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps
  unfolding eval_term.simps
  by (meson bounded_lattice.axioms(3) weak_partial_order.le_cong weak_partial_order_top.axioms(1))

end