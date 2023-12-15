section \<open> Matrix and Vector Auxiliary \<close>

theory Matrix_Vector_Auxiliary

imports "Fishers_Inequality.Matrix_Vector_Extras" 
        
begin 

definition  sum_abs_vec :: "('a :: {abs, comm_monoid_add}) vec \<Rightarrow> 'a " where
"sum_abs_vec v \<equiv> sum (\<lambda> i . \<bar>v $ i\<bar> ) {0..<dim_vec v}"

lemma sum_vec_all_zeros[simp]: "sum_abs_vec vNil = 0"
  by (simp add: sum_abs_vec_def)

lemma sum_vec_all_ones[simp]: "sum_abs_vec (u\<^sub>v n) = n"
  by (simp add: sum_abs_vec_def all_ones_vec_def)

text \<open> The existing vector library contains the identity and zero vectors, a vector with all zeros, but no definition 
of a vector where all elements are -1, as defined below \<close>

definition all_mones_vec ::  "nat \<Rightarrow> 'a :: {zero,uminus,one} vec" ("m\<^sub>v") where
  "m\<^sub>v n \<equiv> vec n (\<lambda> i. (-1))"

lemma dim_vec_all_mones[simp]: "dim_vec (m\<^sub>v n) = n"
  by (simp add: all_mones_vec_def)

lemma all_mones_index [simp]: "i < n \<Longrightarrow> m\<^sub>v n $ i = -1"
  by (simp add: all_mones_vec_def)

lemma sum_vec_all_mones[simp]: "sum_abs_vec (m\<^sub>v n) = n"
  by (simp add: sum_abs_vec_def all_mones_vec_def)

lemma sum_abs_vec_vCons: "sum_abs_vec (vCons a v) = \<bar>a\<bar> + sum_abs_vec v"
proof -
  have 0: "a = (vCons a v) $ 0"
    by simp 
  have "sum_abs_vec v = sum (\<lambda> i . \<bar> v $ i\<bar>) {0..<dim_vec v}" by (simp add: sum_abs_vec_def)
  also have "... = sum (\<lambda> i . \<bar>(vCons a v) $ Suc i\<bar>) {0..< dim_vec v}"
    by force
  also have "... = sum (\<lambda> i . \<bar>(vCons a v) $ i\<bar>) {Suc 0..< (Suc (dim_vec v))}"
    by (smt (verit) sum.cong sum.shift_bounds_Suc_ivl)  
  finally have sum: "sum_abs_vec v = sum (\<lambda> i .  \<bar>(vCons a v) $ i \<bar>) {Suc 0..< dim_vec (vCons a v)}" by simp
  have "sum_abs_vec (vCons a v) = sum (\<lambda> i .  \<bar>(vCons a v) $ i \<bar>){0..< dim_vec (vCons a v)}" 
    by (simp add: sum_abs_vec_def)
  then have "sum_abs_vec (vCons a v) =  \<bar>(vCons a v) $ 0 \<bar> + sum (\<lambda> i .  \<bar>(vCons a v) $ i \<bar>){Suc 0..< dim_vec (vCons a v)}"
    by (metis dim_vec_vCons sum.atLeast_Suc_lessThan zero_less_Suc) 
  thus ?thesis using sum 0 by simp
qed


lemma sum_abs_vec_vCons_lt: 
  assumes "\<And> i. i < dim_vec (vCons a v) \<Longrightarrow>  \<bar>(vCons a v) $ i\<bar> \<le> (n ::int)"
  assumes "sum_abs_vec v \<le> m"
  shows "sum_abs_vec (vCons a v) \<le> n + m"
  by (metis add.commute add_left_mono assms(1) assms(2) dim_vec_vCons_ne_0 dual_order.trans sum_abs_vec_vCons vec_index_vCons_0)

lemma sum_abs_vec_one_zero: 
  assumes "\<And> i. i < dim_vec (v :: int vec) \<Longrightarrow> \<bar>v $ i\<bar> \<le> (1 ::int)"
  shows "sum_abs_vec v \<le> dim_vec v"
  using assms 
  proof (induct v)
    case vNil
    then show ?case by simp
  next
    case (vCons a v)
    then show ?case 
      by (metis Suc_less_eq dim_vec_vCons of_nat_Suc sum_abs_vec_vCons_lt vec_index_vCons_Suc)
  qed

text \<open>Lemmas related counting occurrences of an element in a vector \<close>

lemma count_abs_vec1_sum_non_zero_elements: 
  fixes v :: "'a :: {field_char_0,idom_abs_sgn} vec"
  assumes nn :  "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 0 \<or> v $ i = 1 \<or> v $ i = (-1)"
  shows "of_nat ((count_vec v 1) + (count_vec v (-1))) = sum_abs_vec v"  
  using assms
proof(induct v)
  case vNil
  then show ?case
  by (simp add: count_vec_vNil)
next
  case (vCons a v)
  have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 0 \<or> v $ i = 1 \<or> v $ i = (-1))"
    using vCons.prems by force
  then have IH: "of_nat ((count_vec v 1) + count_vec v (-1)) = sum_abs_vec v"
    using assms vCons.hyps by auto
  have h1: "(\<Sum>i = 0..<dim_vec (vCons a v). \<bar>vCons a v $ i\<bar>) = sum_abs_vec (vCons a v)" 
    by (simp add: sum_abs_vec_def)
   then have h2: "sum (\<lambda>i. \<bar>(vCons a v)$i\<bar>) {0..<dim_vec (vCons a v)} =  \<bar>a\<bar> +  sum_abs_vec (v)"
     by (metis sum_abs_vec_vCons)
   then show ?case 
     using count_vec_vCons dim_vec_vCons_ne_0 sum_abs_vec_vCons vCons.prems vec_index_vCons_0 abs_0 abs_1 abs_minus
     by (smt (verit) IH add.assoc add.commute add_cancel_right_left of_nat_1 of_nat_add one_neq_neg_one)        
qed

lemma count_abs_vec1_three_elems: 
  fixes v :: "'a :: {idom_abs_sgn, field_char_0} vec"
  assumes "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0 \<or> v $ i = (-1))"
  shows "count_vec v 1 + count_vec v 0 + count_vec v (-1) = dim_vec v"
proof-
 have ss: "vec_set v \<subseteq> {0, 1, -1}" using assms by (auto simp add: vec_set_def)
  have "dim_vec v = size (vec_mset v)"
    by (simp add: mset_vec_same_size) 
  have "size (vec_mset v) = (\<Sum> x \<in> (vec_set v) . count (vec_mset v) x)"
    by (simp add: vec_mset_set size_multiset_overloaded_eq) 
  also have  "... = (\<Sum> x \<in> {0, 1, -1} . count (vec_mset v) x)"
 using size_count_mset_ss ss
  by (metis calculation finite.emptyI finite.insertI vec_mset_set)
  finally have "size (vec_mset v) = count (vec_mset v) 1 + count (vec_mset v) 0 + count (vec_mset v) (-1)" 
    by auto
  thus ?thesis
    by (simp add: mset_vec_same_size)
qed


lemma count_abs_vec1_sum_zeros: 
  fixes v :: "'a :: {idom_abs_sgn, field_char_0} vec"
  assumes "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0 \<or> v $ i = (-1)"
  shows "of_nat (count_vec v 0) = of_nat (dim_vec v) - sum_abs_vec v"
  using count_abs_vec1_three_elems count_abs_vec1_sum_non_zero_elements
  by (smt (verit, ccfv_threshold) add_diff_cancel_left' assms diff_diff_eq2 eq_diff_eq of_nat_add)

lemma count_abs_vec1_sum_non_zero_elems_alt: 
  fixes v :: "'a :: {idom_abs_sgn, field_char_0} vec"
  assumes "vec_set v \<subseteq> {0, 1, -1}"
  shows "of_nat (count_vec v 1 + count_vec v (-1)) = sum_abs_vec v"
proof-
  have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0 \<or> v $ i = (-1))" 
    using vec_setI assms by auto
  thus ?thesis 
    by (meson count_abs_vec1_sum_non_zero_elements)
qed

lemma matrl_carrier[simp]:
  "mat_of_rows_list n vs \<in> carrier_mat (length vs) n"
  "dim_row (mat_of_rows_list n vs) = length vs"
  "dim_col (mat_of_rows_list n vs) = n"
  unfolding mat_of_rows_list_def by auto

    
   

end