theory HelperLemmata
  imports Defs
begin

section \<open>The relevant properties of term equality\<close>

(* Reflexivity: t = t *)
lemma eq_reflexive:
  assumes
    "eval_atom_valid L var_st fun_st"
  shows
    "eval_atom (t \<doteq> t) L var_st fun_st"
  unfolding eval_atom.simps(1)
  using assms unfolding eval_atom_valid_def
  by (simp add: bounded_lattice_def lattice.axioms(2) lower_semilattice.axioms(1) partial_order.eq_is_equal)

(* Symmetry: t1 = t2 \<Longrightarrow> t2 = t1 *)
lemma eq_symmetrical:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (t1 \<doteq> t2) L var_st fun_st"
  shows
    "eval_atom (t2 \<doteq> t1) L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps(1)
  by (simp add: bounded_lattice.axioms(1) lattice.axioms(1) partial_order.eq_is_equal upper_semilattice.axioms(1))

(* Transitivity: t1 = t2, t2 = t3 \<Longrightarrow> t1 = t3 *)
lemma eq_transitive:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (t1 \<doteq> t2) L var_st fun_st"
    "eval_atom (t2 \<doteq> t3) L var_st fun_st"
  shows
    "eval_atom (t1 \<doteq> t3) L var_st fun_st"
  using assms
  unfolding eval_atom_valid_def
  unfolding eval_atom.simps(1)
  by (simp add: bounded_lattice.axioms(1) lattice.axioms(1) partial_order.eq_is_equal upper_semilattice.axioms(1))


section \<open>The relevant properties of function application\<close>

(* t=t' \<Longrightarrow> f(t) = f(t') *)
lemma fun_apply_eq:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_term t L var_st fun_st .=\<^bsub>L\<^esub> eval_term t' L var_st fun_st"
  shows
    "eval_term (.f(t)) L var_st fun_st .=\<^bsub>L\<^esub> eval_term (.f(t')) L var_st fun_st"
    using assms unfolding eval_atom_valid_def
    by (metis (full_types)
        BLmf_func.exhaust
        bounded_lattice.axioms(1) eval_term.simps(6) lattice.axioms(2)
        lower_semilattice_def partial_order.eq_is_equal)


section \<open>The relevant properties of function monoticity\<close>
(* The four equivalances used in Proposition 21, Section 3 in the cited paper is formally proved in this section *)
(* Cited paper:
Cantone, D., Zarba, C.G. (2006). A Decision Procedure for Monotone Functions over Bounded and Complete Lattices. In: de Swart, H., Orłowska, E., Schmidt, G., Roubens, M. (eds) Theory and Applications of Relational Structures as Knowledge Instruments II. Lecture Notes in Computer Science(), vol 4342. Springer, Berlin, Heidelberg.
https://doi.org/10.1007/11964810_15
*)

(* inc(f) \<and> dec(f) \<equiv> const(f) *)
lemma const_eq_inc_and_dec:
  assumes "eval_atom_valid L var_st fun_st"
  shows "eval_atom (const(F f)) L var_st fun_st =
  ((eval_atom (inc(F f)) L var_st fun_st) \<and> (eval_atom (dec(F f)) L var_st fun_st))"
  unfolding eval_atom.simps(3-5)
proof
  let ?f = "fun_st f"
  have "bounded_lattice L"
    using assms unfolding eval_atom_valid_def by blast
  then have "weak_partial_order_top L" "weak_partial_order_bottom L"
    by (simp add: bounded_lattice_def)+
  then have "weak_partial_order L"
    by (simp add: weak_partial_order_top_def)

  have "\<And>x y.
   (x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<Longrightarrow>
    ?f x .=\<^bsub>L\<^esub> ?f y \<Longrightarrow>
    ?f x \<sqsubseteq>\<^bsub>L\<^esub> ?f y \<and> ?f y \<sqsubseteq>\<^bsub>L\<^esub> ?f x)"
  proof -
    fix x y assume xy_props: "x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y"
    have "x \<in> carrier L" using xy_props by blast
    have "y \<in> carrier L" using xy_props by blast
    moreover have "?f x \<in> carrier L"
      using \<open>x \<in> carrier L\<close> assms unfolding eval_atom_valid_def by blast
    moreover have "?f y \<in> carrier L"
      using \<open>y \<in> carrier L\<close> assms unfolding eval_atom_valid_def by blast
    moreover assume eq: "?f x .=\<^bsub>L\<^esub> ?f y"
    ultimately show "?f x \<sqsubseteq>\<^bsub>L\<^esub> ?f y \<and> ?f y \<sqsubseteq>\<^bsub>L\<^esub> ?f x" using \<open>weak_partial_order L\<close>
      by (metis equivalence.sym weak_partial_order.weak_refl weak_partial_order_def)
  qed
  then show "\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<longrightarrow> ?f x .=\<^bsub>L\<^esub> ?f y \<Longrightarrow>
    (\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longrightarrow> ?f x \<sqsubseteq>\<^bsub>L\<^esub> ?f y) \<and>
    (\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longrightarrow> ?f y \<sqsubseteq>\<^bsub>L\<^esub> ?f x)" by blast

  show "(\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longrightarrow> fun_st f x \<sqsubseteq>\<^bsub>L\<^esub> fun_st f y) \<and>
    (\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longrightarrow> fun_st f y \<sqsubseteq>\<^bsub>L\<^esub> fun_st f x) \<Longrightarrow>
    \<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<longrightarrow> fun_st f x .=\<^bsub>L\<^esub> fun_st f y"
  proof (standard, standard, standard)
    fix x y assume xy:
       "(\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longrightarrow> ?f x \<sqsubseteq>\<^bsub>L\<^esub> ?f y) \<and>
        (\<forall>x y. x \<in> carrier L \<and> y \<in> carrier L \<and> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longrightarrow> ?f y \<sqsubseteq>\<^bsub>L\<^esub> ?f x)"
       "x \<in> carrier L \<and> y \<in> carrier L"
    then have "?f x \<in> carrier L" "?f y \<in> carrier L"
      using assms unfolding eval_atom_valid_def by blast+
    have "x \<in> carrier L" "y \<in> carrier L"
      using xy by blast+
    let ?z = "eval_term .1 L var_st fun_st"
    have "x \<sqsubseteq>\<^bsub>L\<^esub> ?z" "y \<sqsubseteq>\<^bsub>L\<^esub> ?z"
      unfolding eval_term.simps(2) using \<open>x \<in> carrier L\<close> \<open>y \<in> carrier L\<close> \<open>weak_partial_order_top L\<close>
      by (simp add: weak_partial_order_top.top_higher)+
    have "?f ?z \<in> carrier L"
      using assms unfolding eval_atom_valid_def
      by (simp add: \<open>weak_partial_order_top L\<close> weak_partial_order_top.top_closed)
    
    have "?f x \<sqsubseteq>\<^bsub>L\<^esub> ?f ?z" "?f ?z \<sqsubseteq>\<^bsub>L\<^esub> ?f x"
      using xy \<open>weak_partial_order_top L\<close> \<open>x \<sqsubseteq>\<^bsub>L\<^esub> ?z\<close> weak_partial_order_top.top_closed
      by auto blast
    then have "?f x .=\<^bsub>L\<^esub> ?f ?z"
      using \<open>?f x \<in> carrier L\<close> \<open>?f ?z \<in> carrier L\<close> \<open>weak_partial_order L\<close>
      by (simp add: weak_partial_order.weak_le_antisym)

    moreover have "?f y \<sqsubseteq>\<^bsub>L\<^esub> ?f ?z" "?f ?z \<sqsubseteq>\<^bsub>L\<^esub> ?f y"
      using xy \<open>weak_partial_order_top L\<close> \<open>y \<sqsubseteq>\<^bsub>L\<^esub> ?z\<close> weak_partial_order_top.top_closed
      by auto blast
    then have "?f y .=\<^bsub>L\<^esub> ?f ?z"
      using \<open>?f y \<in> carrier L\<close> \<open>?f ?z \<in> carrier L\<close> \<open>weak_partial_order L\<close>
      by (simp add: weak_partial_order.weak_le_antisym)

    ultimately show "?f x .=\<^bsub>L\<^esub> ?f y"
      using \<open>?f x \<in> carrier L\<close> \<open>?f y \<in> carrier L\<close> \<open>?f ?z \<in> carrier L\<close> \<open>weak_partial_order L\<close>
      by (meson equivalence.sym equivalence.trans weak_partial_order_def)
  qed
qed

(* inc(f) \<and> const(f) \<equiv> const(f) *)
lemma const_eq_inc_and_const:
  assumes "eval_atom_valid L var_st fun_st"
  shows "eval_atom (const(F f)) L var_st fun_st =
  ((eval_atom (inc(F f)) L var_st fun_st) \<and> (eval_atom (const(F f)) L var_st fun_st))"
  using assms const_eq_inc_and_dec by blast

(* dec(f) \<and> const(f) \<equiv> const(f) *)
lemma const_eq_dec_and_const:
  assumes "eval_atom_valid L var_st fun_st"
  shows "eval_atom (const(F f)) L var_st fun_st =
  ((eval_atom (dec(F f)) L var_st fun_st) \<and> (eval_atom (const(F f)) L var_st fun_st))"
  using assms const_eq_inc_and_dec by blast

(* inc(f) \<and> dec(f) \<and> const(f) \<equiv> const(f) *)
lemma const_eq_inc_and_dec_and_const:
  assumes "eval_atom_valid L var_st fun_st"
  shows "eval_atom (const(F f)) L var_st fun_st =
  ((eval_atom (inc(F f)) L var_st fun_st) \<and> (eval_atom (dec(F f)) L var_st fun_st) \<and> (eval_atom (const(F f)) L var_st fun_st))"
  using assms const_eq_inc_and_dec by blast


section \<open>Substitution\<close>

(* x = y \<Longrightarrow> t = t[x/y] *)
lemma subst_vv_term_eq:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x \<doteq> V y) L var_st fun_st"
  shows
    "eval_atom (t \<doteq> (subst_vv_term t x y)) L var_st fun_st"
proof (induction t)
  case (V x')
  then show ?case
  proof (cases "x' = x")
    case True
    then have "subst_vv_term (V x') x y = V y"
      unfolding subst_vv_term.simps(1) by simp
    then show ?thesis
      using True assms(2) by auto
  next
    case False
    then have "subst_vv_term (V x') x y = V x'"
      unfolding subst_vv_term.simps(1) by simp
    then show ?thesis
      using eq_reflexive assms(1) by metis
  qed
next
  case Const1
  have "subst_vv_term .1 x y = .1" by simp
  then show ?case
    using eq_reflexive assms(1) by metis
next
  case Const0
  have "subst_vv_term .0 x y = .0" by simp
  then show ?case
    using eq_reflexive assms(1) by metis
next
  case (Meet t1 t2)
  then show ?case
    using assms(1) unfolding eval_atom_valid_def
    unfolding eval_atom.simps(1)
    by (simp add: bounded_lattice_def lattice_def lower_semilattice.axioms(1) partial_order.eq_is_equal)
next
  case (Join t1 t2)
  then show ?case
    using assms(1) unfolding eval_atom_valid_def
    unfolding eval_atom.simps(1)
    by (simp add: bounded_lattice_def lattice_def lower_semilattice.axioms(1) partial_order.eq_is_equal)
next
  case (FuncApp f t)
  then show ?case
    using FuncApp
    using assms(1)
    unfolding eval_atom.simps(1) subst_vv_term.simps(4)
    unfolding eval_term.simps
    using fun_apply_eq
    by blast
qed

(* x = 0 \<Longrightarrow> t = t[x/0] *)
lemma subst_v0_term_eq:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x \<doteq> .0) L var_st fun_st"
  shows
    "eval_atom (t \<doteq> (subst_v0_term t x)) L var_st fun_st"
  using assms
proof (induction t)
  case (V y)
  then show ?case
    unfolding subst_v0_term.simps
    by (metis (full_types) eq_reflexive)
next
  case Const1
  then show ?case
    unfolding subst_v0_term.simps
    using eq_reflexive by blast
next
  case Const0
  then show ?case
    unfolding subst_v0_term.simps
    using eq_reflexive by blast
next
  case (Meet t1 t2)
  then show ?case
    unfolding subst_v0_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(4)
    by (metis (full_types)
        eval_atom_valid_def
        bounded_lattice.axioms(1) lattice_def upper_semilattice.axioms(1)
        partial_order.eq_is_equal)
next
  case (Join t1 t2)
  then show ?case
    unfolding subst_v0_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(5)
    by (metis (full_types)
        eval_atom_valid_def
        bounded_lattice.axioms(1) lattice_def upper_semilattice.axioms(1)
        partial_order.eq_is_equal)
next
  case (FuncApp f t)
  then show ?case
    unfolding subst_v0_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(6)
    using fun_apply_eq
    by blast
qed

(* 0 = x \<Longrightarrow> t = t[0/x] *)
lemma subst_0v_term_eq:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (.0 \<doteq> V x) L var_st fun_st"
  shows
    "eval_atom (t \<doteq> (subst_0v_term t x)) L var_st fun_st"
  using assms
proof (induction t)
  case (V y)
  then show ?case
    unfolding subst_0v_term.simps
    by (metis (full_types) eq_reflexive)
next
  case Const1
  then show ?case
    unfolding subst_0v_term.simps
    using eq_reflexive by blast
next
  case Const0
  then show ?case
    unfolding subst_0v_term.simps
    using eq_reflexive by blast
next
  case (Meet t1 t2)
  then show ?case
    unfolding subst_0v_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(4)
    by (metis (full_types)
        eval_atom_valid_def
        bounded_lattice.axioms(1) lattice_def upper_semilattice.axioms(1)
        partial_order.eq_is_equal)
next
  case (Join t1 t2)
  then show ?case
    unfolding subst_0v_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(5)
    by (metis (full_types)
        eval_atom_valid_def
        bounded_lattice.axioms(1) lattice_def upper_semilattice.axioms(1)
        partial_order.eq_is_equal)
next
  case (FuncApp f t)
  then show ?case
    unfolding subst_0v_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(6)
    using fun_apply_eq
    by blast
qed

(* x = 1 \<Longrightarrow> t = t[x/1] *)
lemma subst_v1_term_eq:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (V x \<doteq> .1) L var_st fun_st"
  shows
    "eval_atom (t \<doteq> (subst_v1_term t x)) L var_st fun_st"
  using assms
proof (induction t)
  case (V y)
  then show ?case
    unfolding subst_v1_term.simps
    by (metis (full_types) eq_reflexive)
next
  case Const1
  then show ?case
    unfolding subst_v1_term.simps
    using eq_reflexive by blast
next
  case Const0
  then show ?case
    unfolding subst_v1_term.simps
    using eq_reflexive by blast
next
  case (Meet t1 t2)
  then show ?case
    unfolding subst_v1_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(4)
    by (metis (full_types)
        eval_atom_valid_def
        bounded_lattice.axioms(1) lattice_def upper_semilattice.axioms(1)
        partial_order.eq_is_equal)
next
  case (Join t1 t2)
  then show ?case
    unfolding subst_v1_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(5)
    by (metis (full_types)
        eval_atom_valid_def
        bounded_lattice.axioms(1) lattice_def upper_semilattice.axioms(1)
        partial_order.eq_is_equal)
next
  case (FuncApp f t)
  then show ?case
    unfolding subst_v1_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(6)
    using fun_apply_eq
    by blast
qed

(* 1 = x \<Longrightarrow> t = t[1/x] *)
lemma subst_1v_term_eq:
  assumes
    "eval_atom_valid L var_st fun_st"
    "eval_atom (.1 \<doteq> V x) L var_st fun_st"
  shows
    "eval_atom (t \<doteq> (subst_1v_term t x)) L var_st fun_st"
  using assms
proof (induction t)
  case (V y)
  then show ?case
    unfolding subst_1v_term.simps
    by (metis (full_types) eq_reflexive)
next
  case Const1
  then show ?case
    unfolding subst_1v_term.simps
    using eq_reflexive by blast
next
  case Const0
  then show ?case
    unfolding subst_1v_term.simps
    using eq_reflexive by blast
next
  case (Meet t1 t2)
  then show ?case
    unfolding subst_1v_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(4)
    by (metis (full_types)
        eval_atom_valid_def
        bounded_lattice.axioms(1) lattice_def upper_semilattice.axioms(1)
        partial_order.eq_is_equal)
next
  case (Join t1 t2)
  then show ?case
    unfolding subst_1v_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(5)
    by (metis (full_types)
        eval_atom_valid_def
        bounded_lattice.axioms(1) lattice_def upper_semilattice.axioms(1)
        partial_order.eq_is_equal)
next
  case (FuncApp f t)
  then show ?case
    unfolding subst_1v_term.simps
    unfolding eval_atom.simps(1)
    unfolding eval_term.simps(6)
    using fun_apply_eq
    by blast
qed


end