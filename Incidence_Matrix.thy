theory Incidence_Matrix
  imports Network_Incidence_System 
          "List-Index.List_Index" 
          "HOL.Relation" 
          "HOL.Set_Interval"
          "Fishers_Inequality.Matrix_Vector_Extras"
          Matrix_Vector_Auxiliary 
begin

text \<open>Enable coercion of nats to reals to assist with reasoning on network properties\<close>
declare [[coercion_enabled]]
declare [[coercion "of_nat :: nat \<Rightarrow> real"]]

subsection \<open> Incidence Vector\<close>

definition incidence_vec :: "'a nodes \<Rightarrow> 'a edge \<Rightarrow> ('b :: {field_char_0} vec)" where
"incidence_vec Ns p \<equiv> vec (length Ns) (\<lambda>i. if (Ns!i) = fst p \<and> (fst p \<noteq> snd p) then 1 else if  (Ns!i) = snd p \<and> (fst p \<noteq> snd p) then -1 else 0)"

lemma incidence_vec_elems: "set\<^sub>v (incidence_vec Ns p) \<subseteq> {0, 1, -1}"
by (auto simp add: vec_set_def incidence_vec_def)

lemma finite_neg_inci_vec_elems: "finite (set\<^sub>v (incidence_vec Ns p))"
using finite_subset incidence_vec_elems by blast

lemma incidence_vec_dim: "dim_vec (incidence_vec Ns p) = length Ns" by (simp add: incidence_vec_def)

lemma incidence_vec_index: "i < length Ns \<Longrightarrow> incidence_vec Ns p $ i = (if (fst p \<noteq> snd p) \<and> (Ns!i) = fst p then 1 else if (fst p \<noteq> snd p) \<and> (Ns!i) = snd p then -1 else 0)"
by(simp add: incidence_vec_def)

lemma incidence_vec_index_mone: "i < length Ns \<Longrightarrow> fst p \<noteq> snd p \<Longrightarrow> incidence_vec Ns p $ i = -1 \<longleftrightarrow>  (Ns ! i) = snd p"
  by (simp add: incidence_vec_index)

lemma incidence_vec_index_zero: "i < length Ns \<Longrightarrow>  fst p \<noteq> snd p \<Longrightarrow> incidence_vec Ns p $ i = 0 \<longleftrightarrow> (Ns ! i) \<noteq> snd p \<and> (Ns ! i) \<noteq> fst p"
by(simp add: incidence_vec_def)

lemma incidence_vec_index_zero_case1: "i < length Ns \<Longrightarrow> (fst p = snd p) \<Longrightarrow> incidence_vec Ns p $ i = 0 \<Longrightarrow> (Ns ! i) \<noteq> snd p \<Longrightarrow> (Ns ! i) \<noteq> fst p"
  by presburger

lemma incidence_vec_index_one: "i < length Ns \<Longrightarrow> fst p \<noteq> snd p \<Longrightarrow> incidence_vec Ns p $ i = 1 \<longleftrightarrow>  (Ns ! i) = fst p"
  by(simp add: incidence_vec_def)

subsection \<open>A network represented by a directed graph without self-loops is characterized by its Incidence Matrix whose entries 0, 1, -1\<close>

definition incidence_matrix :: "'a nodes \<Rightarrow> 'a edges  \<Rightarrow> ('b :: {field_char_0}) mat" where
"incidence_matrix Ns Es  \<equiv>  mat (length Ns) (length Es) (\<lambda>(i,j). if (fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = fst (Es!j)) then 1  else if (fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = snd (Es!j)) then -1 else 0)"

lemma inci_matcol_dim: "dim_col (incidence_matrix Ns Es) = size Es" by (simp add: incidence_matrix_def)

lemma inci_matrow_dim: "dim_row (incidence_matrix Ns Es) = length Ns" by (simp add: incidence_matrix_def)

lemma incidence_mat_elems: "elements_mat (incidence_matrix Ns Es) \<subseteq> {0, 1, -1}"
by (auto simp add: elements_mat_def incidence_matrix_def)

lemma finite_incidence_mat_elems: "finite (elements_mat (incidence_matrix Ns Es))"
using finite_subset incidence_mat_elems by blast

lemma incidence_index[simp]: "i<length Ns \<Longrightarrow> j < size Es \<Longrightarrow> 
incidence_matrix Ns Es  = mat (length Ns) (length Es) (\<lambda>(i,j). if (fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = fst (Es!j)) then 1  else if (fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = snd (Es!j)) then -1 else 0)"
unfolding incidence_matrix_def by auto

lemma incidence_carrier[simp]: "incidence_matrix Ns Es \<in> carrier_mat (length Ns) (size Es)" 
  unfolding carrier_mat_def by (auto simp add: inci_matcol_dim inci_matrow_dim)

lemma inci_matrix_pos: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = fst (Es!j)
    \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 1"
    unfolding incidence_matrix_def by auto

lemma inci_matrix_neg: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = snd (Es!j)
    \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = -1"
  unfolding incidence_matrix_def by auto    

lemma inci_matrix_0_case1: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) = snd (Es!j))
    \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0"
  by(simp add: incidence_matrix_def)

lemma inci_matrix_0_case2: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> (Ns!i) \<noteq> fst (Es!j) \<Longrightarrow> (Ns!i) \<noteq> snd (Es!j)
    \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0"
  using incidence_matrix_def by auto

lemma inci_matrix_mone_neg: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = -1 \<Longrightarrow> 
   (Ns!i) = snd (Es!j)"
  by (metis inci_matrix_0_case2 inci_matrix_pos one_neq_neg_one zero_neq_neg_one)

lemma inci_matrix_one_pos: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 1
    \<Longrightarrow> (Ns!i) = fst (Es!j)"
  by (metis inci_matrix_0_case2 inci_matrix_neg one_neq_neg_one one_neq_zero)

lemma inci_matrix_zero_no_case1: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow>  (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0  \<Longrightarrow>
   (Ns!i) \<noteq> fst (Es!j) \<and>  (Ns!i) \<noteq> snd (Es!j)"
  by (metis inci_matrix_neg inci_matrix_pos zero_neq_neg_one zero_neq_one)

lemma inci_matrix_zero_no_incident: "i < length Ns \<Longrightarrow> j < length Es  \<Longrightarrow> (fst (Es!j) = snd (Es!j)) \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0 \<Longrightarrow> 
   (Ns!i) \<noteq> fst (Es!j) \<Longrightarrow> (Ns!i) \<noteq> snd (Es!j)"
  by presburger

lemma inci_matrix_one_pos_iff:  "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow>  (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (incidence_matrix Ns Es) $$ (i, j) = 1 \<longleftrightarrow> Ns ! i = fst (Es ! j)"
  using inci_matrix_pos inci_matrix_one_pos by metis

lemma inci_matrix_mone_neg_iff:  "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow>  (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (incidence_matrix Ns Es) $$ (i, j) = -1 \<longleftrightarrow> Ns ! i = snd (Es ! j)"
  using inci_matrix_neg inci_matrix_mone_neg by auto

lemma inci_matrix_zero_iff1:  "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow>  (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (incidence_matrix Ns Es) $$ (i, j) = 0 \<longleftrightarrow>  (Ns!i) \<noteq> fst (Es!j) \<and> (Ns!i) \<noteq> snd (Es!j)"
  using inci_matrix_0_case1 inci_matrix_zero_no_case1 by auto

lemma inci_matrix_one_implies_snd: "F \<subseteq> {..< length Ns} \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (\<And> i. i\<in>F \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 1) \<Longrightarrow> i \<in> F \<Longrightarrow> Ns ! i = fst (Es ! j)"
  using inci_matrix_one_pos_iff by blast

lemma inci_matrix_mone_implies_fst: "F \<subseteq> {..< length Ns} \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (\<And> i. i\<in>F \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = -1) \<Longrightarrow> i \<in> F \<Longrightarrow> Ns ! i = snd (Es ! j)"
  using inci_matrix_mone_neg_iff by blast

lemma inci_matrix_zero_implies_noincident: "F \<subseteq> {..< length Ns} \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (\<And> i. i\<in>F \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0) \<Longrightarrow> i \<in> F \<Longrightarrow> Ns ! i \<noteq> fst  (Es ! j) \<and> Ns ! i \<noteq> snd  (Es ! j)"
  using inci_matrix_zero_iff1 by blast


text \<open>Reasoning on Columns/Rows of the generalized incidence matrix\<close>

lemma incidence_matrix_col_def:  "j < length Es \<Longrightarrow> i < length Ns \<Longrightarrow> 
    (col (incidence_matrix Ns Es) j) $ i = (if fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = fst (Es!j) then 1 else if fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = snd (Es!j) then -1 else 0)"
  by (simp add: incidence_matrix_def)

lemma incidence_mat_col_list_map_elem: "j < length Es \<Longrightarrow> i < length Ns \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow>
    col (incidence_matrix Ns Es) j $ i = map_vec 
    (\<lambda> x . if  (x = fst (Es ! j)) then 1 else if (x = snd (Es ! j)) then -1 else 0) (vec_of_list Ns) $ i"
  by (simp add: incidence_matrix_col_def vec_of_list_index)

lemma inci_mat_col_list_map:  "j < length Es \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow>
    col (incidence_matrix Ns Es) j = map_vec (\<lambda> x . if (x = fst (Es ! j)) then 1 else if (x = snd (Es ! j)) then -1 else 0) (vec_of_list Ns)"
 by (intro eq_vecI,
    simp_all add: inci_matcol_dim inci_matrow_dim incidence_mat_col_list_map_elem index_vec_of_list incidence_matrix_def)

lemma incidence_matrix_row_def:  "j < length Es \<Longrightarrow> i < length Ns \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow>
    (row (incidence_matrix Ns Es) i) $ j = (if (Ns!i) = fst (Es!j) then 1 else if (Ns!i) = snd (Es!j) then -1 else 0)"
  by (simp add: incidence_matrix_def)

lemma incidence_matrix_row_list_map_elem: "j < length Es \<Longrightarrow> i < length Ns \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow>
    row (incidence_matrix Ns Es) i $ j = map_vec (\<lambda> b . if ((Ns ! i) = fst b) then 1 else if ((Ns ! i) = snd b) then -1 else 0) (vec_of_list Es) $ j"
  by(simp add: incidence_matrix_def vec_of_list_index)

lemma inci_mat_row_list_map:  "i < length Ns \<Longrightarrow> 
    row (incidence_matrix Ns Es) i = map_vec (\<lambda> b . if  (fst b \<noteq> snd b) \<and> (Ns ! i)= fst b then 1 else if  (fst b \<noteq> snd b) \<and> (Ns ! i)= snd b then -1 else 0) (vec_of_list Es)"
 by (smt (z3) dim_vec_of_list eq_vecI inci_matcol_dim inci_matrix_0_case1 inci_matrow_dim incidence_matrix_row_def index_map_vec(1) index_map_vec(2) index_row(1) index_row(2) index_vec_of_list)

text \<open>Connection between incidence vector and the incidence matrix\<close>

lemma incidence_mat_inci_colvec: "j < length Es \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow> col (incidence_matrix Ns Es) j = incidence_vec Ns (Es ! j)"
  by (auto simp add: incidence_matrix_def incidence_vec_def)

lemma inc_mat_of_cols_inc_vecs: 
  assumes "\<forall>j \<in> {0..< length Es}. fst (Es!j) \<noteq> snd (Es!j)"
  shows "cols (incidence_matrix Ns Es) = map (\<lambda> j . incidence_vec Ns j) Es"
proof (intro nth_equalityI)
  have l1: "length (cols (incidence_matrix Ns Es)) = length Es"
    using inci_matcol_dim by simp
  have l2: "length (map (\<lambda> j . incidence_vec Ns j) Es) = length Es"
    using length_map by simp
  then show "length (cols (incidence_matrix Ns Es)) = length (map (incidence_vec Ns) Es)" 
    using l1 l2 by simp
  show "\<And>i. i < length (cols (incidence_matrix Ns Es)) \<Longrightarrow> cols (incidence_matrix Ns Es) ! i = map (incidence_vec Ns) Es ! i "
    using incidence_mat_inci_colvec l1 
    by (metis assms atLeastLessThan_iff cols_length cols_nth linorder_not_le not_less_zero nth_map)
qed


text \<open>Network system properties for the incidence matrices\<close>

definition all_zeros_row :: "('a :: {field_char_0}) mat \<Rightarrow>  nat \<Rightarrow> bool" where
"all_zeros_row A i \<equiv>  \<forall> i< dim_row A. (\<forall> j< dim_col A.  row A i $ j = 0)"

definition isolated_node :: "('a :: {field_char_0}) mat \<Rightarrow> nat \<Rightarrow> bool" where
"isolated_node A i  \<equiv> all_zeros_row A i"

definition mat_in_degree_num :: "('a :: {field_char_0}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_in_degree_num A i  \<equiv> count_vec (row A i) (1)"

definition mat_out_degree_num :: "('a :: {field_char_0}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_out_degree_num A i  \<equiv> count_vec (row A i) (-1)"

definition mat_degree_num :: "'a :: {field_char_0} mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_degree_num A i  \<equiv> mat_in_degree_num A i + mat_out_degree_num A i"

definition zeros_in_row :: "'a :: {field_char_0} mat \<Rightarrow> nat \<Rightarrow> nat" where
"zeros_in_row A i  \<equiv>  count_vec (row A i) 0"

definition mat_degree_of_node :: "'a :: {field_char_0} mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_degree_of_node A i  \<equiv> dim_row A - zeros_in_row A i"

lemma mat_degree_property: 
  fixes A :: "'a :: {field_char_0, idom_abs_sgn} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> of_nat (mat_degree_num A i) = sum_abs_vec (row A i)"
  unfolding mat_degree_num_def mat_in_degree_num_def  mat_out_degree_num_def
   using row_elems_subset_mat subset_trans 
   by (metis assms count_abs_vec1_sum_non_zero_elems_alt)


lemma A_not_zero_simp: 
  fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i, j) \<noteq> 0 \<Longrightarrow> A $$ (i, j) = 1 \<or> A $$ (i, j) = -1"
  using assms by auto

lemma A_not_zero_one_simp: 
  fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i, j) \<noteq> 0 \<Longrightarrow> A $$ (i, j) \<noteq> 1 \<Longrightarrow> A $$ (i, j) = -1"
  using assms by auto

lemma A_not_mone_zero_simp: 
fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i, j) \<noteq> 0 \<Longrightarrow> A $$ (i, j) \<noteq> -1 \<Longrightarrow> A $$ (i, j) = 1"
  using assms by blast

lemma A_not_mone_one_simp: 
  fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i, j) \<noteq> 1 \<Longrightarrow> A $$ (i, j) \<noteq> -1 \<Longrightarrow> A $$ (i, j) = 0"
  using assms by blast


lemma A_index_square_abs_itself:
  fixes A :: "'a :: {field_char_0,idom_abs_sgn} mat"
  assumes ee: "elements_mat A \<subseteq> {0, 1, -1}"
  shows"i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> (A $$ (i, j))^2 = abs (A $$ (i, j))"
  using assms  by fastforce
  

lemma A_row_index_square_abs_itself:
 fixes A :: "'a :: {field_char_0,idom_abs_sgn} mat"
 assumes "elements_mat A \<subseteq> {0, 1, -1}"
 shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> ((row A i) $ j) ^ 2 = abs ((row A i) $ j)"
  using A_index_square_abs_itself assms by auto

text \<open>Alternate way of degree representing by product of row matrices\<close>

lemma scalar_prod_inc_vec_degree_num_mat:
   fixes A :: "'a :: {field_char_0,idom_abs_sgn} mat"
   assumes "i < dim_row A"
   assumes ee :"elements_mat A \<subseteq> {0, 1, -1}"
  shows "(row A i) \<bullet> (row A i) = of_nat (mat_degree_num A i)"
proof-
  have "(row A i) \<bullet> (row A i) = (\<Sum> j \<in> {0..<dim_col A} . (row A i) $ j * (row A i) $ j)" 
    using assms scalar_prod_def sum.cong 
     by (metis (no_types, lifting) index_row(2))
   also have "... = (\<Sum> j \<in> {0..<dim_col A} . ((row A i) $ j)^2)"
     by (metis power2_eq_square)
   also have "... = (\<Sum> j \<in> {0..<dim_col A} . abs ((row A i) $ j))"
    using A_row_index_square_abs_itself 
    by (metis (no_types, lifting) assms(1) ee sum.ivl_cong)
  finally show ?thesis using sum_abs_vec_def mat_degree_property ee assms(1)
    by (metis index_row(2))
qed

 

context nonempty_network_system
begin 

abbreviation K :: "real mat" where
"K \<equiv> incidence_matrix \<N>s \<E>s"

lemma K_alt_def:"K = mat m n (\<lambda> (i,j). if pos_incident (\<N>s!i) (\<E>s!j) then 1 else if neg_incident (\<N>s!i) (\<E>s!j) then -1 else 0)"
  unfolding incidence_matrix_def using neg_incident_netw_altdef pos_incident_netw_altdef wf_network_system wf_network_system_iff by auto


lemma pos_inc_K_one: "i < dim_row K \<Longrightarrow> j < dim_col K \<Longrightarrow> pos_incident (\<N>s!i) (\<E>s!j) \<Longrightarrow> K $$ (i,j) = 1"
  using K_alt_def pos_incident_netw_altdef by fastforce

lemma neg_inc_K_mone: "i < dim_row K \<Longrightarrow> j < dim_col K \<Longrightarrow> neg_incident (\<N>s!i) (\<E>s!j) \<Longrightarrow> K $$ (i,j) = -1"
  using K_alt_def neg_incident_netw_altdef by fastforce

lemma no_inc_K_zero: "i < dim_row K \<Longrightarrow> j < dim_col K \<Longrightarrow> \<not> neg_incident (\<N>s!i) (\<E>s!j) \<Longrightarrow> \<not> pos_incident (\<N>s!i) (\<E>s!j) \<Longrightarrow> K $$ (i,j) = 0"
  by (simp add: K_alt_def)


text \<open>Matrix Dimension related lemmas \<close>
 
lemma K_carrier_mat: "K \<in> carrier_mat m n" 
  by (simp add: incidence_matrix_def)

lemma dim_row_K[simp]: "dim_row K = m"
  using inci_matrow_dim by auto

lemma dim_col_K[simp]: "dim_col K = n"
  using inci_matcol_dim by auto 

lemma dim_vec_row_K: "dim_vec (row K i) = n"
  by simp

lemma dim_vec_col_K: "dim_vec (col K i) = m" by simp 

lemma dim_vec_K_col: 
  assumes "j < n"
  shows "dim_vec (cols K ! j) = m"
  by (simp add: assms incidence_vec_dim)

lemma K_elems: "elements_mat (K) \<subseteq> {0, 1, -1}"
  by (auto simp add: incidence_matrix_def elements_mat_def)

text \<open>Transpose properties \<close>

lemma transpose_K_mult_dim: "dim_row (K * K\<^sup>T) = m" "dim_col (K * K\<^sup>T) = m"
  by (simp_all)

lemma K_trans_index_val: "i < dim_col K \<Longrightarrow> j < dim_row K \<Longrightarrow> 
    K\<^sup>T $$ (i, j) = (if pos_incident (\<N>s!j) (\<E>s!i) then 1 else if 
 neg_incident (\<N>s!j) (\<E>s!i) then -1 else 0)"
  using K_alt_def by simp

lemma transpose_entries: "elements_mat (K\<^sup>T) \<subseteq> {0, 1, -1}"
  by (metis K_elems transpose_mat_elems)
 
text \<open>Matrix element and index related lemmas \<close>

lemma K_mat_row_elems: "i < m \<Longrightarrow> vec_set (row K i) \<subseteq> {0, 1, -1}"
  by (metis K_elems dim_row_K row_elems_subset_mat subset_trans)

lemma K_mat_col_elems: "j < n \<Longrightarrow> vec_set (col K j) \<subseteq> {0, 1, -1}"
  by (metis K_elems col_elems_subset_mat dim_col_K subset_trans)

lemma K_matrix_elems_one_mone_zero: "i < m \<Longrightarrow> j < n \<Longrightarrow> K $$ (i, j) = 0 \<or> K $$ (i, j) = 1 \<or> K $$ (i, j) = -1" 
  by (simp add: incidence_matrix_def)

lemma K_not_zero_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> 0 \<Longrightarrow> K $$ (i, j) = 1 \<or> K $$ (i, j) = -1"
  using incidence_mat_elems[of "\<N>s" "\<E>s"]
  by (smt (verit, best) dim_col_K dim_row_K incidence_matrix_col_def index_col)

lemma K_not_one_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> 1 \<Longrightarrow> K $$ (i, j) = 0 \<or> K $$ (i, j) = -1"
  using incidence_mat_elems
  by (smt (verit, best) dim_col_K dim_row_K incidence_matrix_col_def index_col)

lemma K_not_mone_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> -1 \<Longrightarrow> K $$ (i, j) = 0 \<or> K $$ (i, j) = 1"
  using incidence_mat_elems
  by (smt (verit, best) dim_col_K dim_row_K incidence_matrix_col_def index_col)

lemma K_not_Mone_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> 1 \<Longrightarrow> K $$ (i, j) \<noteq> -1 \<Longrightarrow> K $$ (i, j) = 0"
  using K_not_mone_simp by blast

lemma K_matrix_pos_iff: "i < m \<Longrightarrow> j < n \<Longrightarrow> K $$ (i, j) = 1 \<longleftrightarrow> \<N>s!i = fst (\<E>s!j) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j)"
  using inci_matrix_one_pos_iff no_self_loop valid_edges_index by blast

lemma K_matrix_neg_iff: "i < m \<Longrightarrow> j < n \<Longrightarrow>  K $$ (i, j) = -1 \<longleftrightarrow> \<N>s !i = snd (\<E>s!j) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) "
  using inci_matrix_mone_neg_iff by (metis wf_network_system_iff nth_mem wf_network_system)

lemma K_matrix_zero_iff: "i < m \<Longrightarrow> j < n \<Longrightarrow> K $$ (i, j) = 0 \<longleftrightarrow> \<N>s !i \<noteq> fst (\<E>s!j) \<and> \<N>s !i \<noteq> snd (\<E>s!j)"
  by (meson in_set_conv_nth inci_matrix_zero_iff1 network_wf)


lemma K_index_square_itself: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> (K $$ (i, j))^2 = abs (K $$ (i, j))"
  using K_not_zero_simp by fastforce

lemma K_row_index_square_itself: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> ((row K i) $ j)^2 = abs ((row K i) $ j)"
  using index_row  K_index_square_itself by auto 

lemma K_col_def_conv_pos: "j < n \<Longrightarrow> i < m \<Longrightarrow> (col K j) $ i = 1 \<Longrightarrow> (\<N>s!i) = fst (\<E>s!j) \<and>  fst (\<E>s!j) \<noteq> snd (\<E>s!j)\<Longrightarrow> (pos_incident (\<N>s!i) (\<E>s!j))"
  using pos_incident_cond_indexed by blast

lemma K_col_def_conv_mone: "j < n \<Longrightarrow> i < m \<Longrightarrow> (col K j) $ i = -1 \<Longrightarrow> (\<N>s!i) = snd (\<E>s!j) \<and>  fst (\<E>s!j) \<noteq> snd (\<E>s!j)"
proof -
  assume a1: "col K j $ i = - 1"
  assume a2: "i < m"
  assume a3: "j < n"
  then have "\<E>s ! j \<in> \<E>"
    using nth_mem by blast
  then have "network_system \<N>s \<E>s \<and> \<E>s ! j \<in> \<E>"
    using wf_network_system by force
  then have "fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)"
    using network_system.network_wf by blast
  then show ?thesis
    using a3 a2 a1
    by (metis incidence_mat_inci_colvec incidence_vec_index_mone)
qed


text \<open>Incidence Vector's of Incidence Matrix columns \<close>

lemma col_incidence_vec: "j < length \<E>s \<Longrightarrow> incidence_vec \<N>s (\<E>s ! j) = col K j"
  by (metis incidence_mat_inci_colvec network_system.network_wf nth_mem wf_network_system)

text \<open>Incidence matrix column properties\<close>

lemma K_col_def: "j < n \<Longrightarrow> i < m \<Longrightarrow> (col K j) $ i = (if (\<N>s!i) = fst (\<E>s!j) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else if (\<N>s!i) = snd (\<E>s!j)  \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0)"
  using incidence_matrix_col_def 
  by (simp add: network_wf)

lemma K_col_def_indiv: "j < n \<Longrightarrow> i < m \<Longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j) \<Longrightarrow> (\<N>s!i) = fst (\<E>s!j) \<Longrightarrow> (col K j) $ i = 1"
     "j < n \<Longrightarrow> i < m  \<Longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j) \<Longrightarrow> (\<N>s!i) = snd (\<E>s!j) \<Longrightarrow> (col K j) $ i = -1"
     "j < n \<Longrightarrow> i < m \<Longrightarrow> (\<N>s!i) \<noteq> fst (\<E>s!j) \<Longrightarrow>  (\<N>s!i) \<noteq> snd (\<E>s!j) \<Longrightarrow> (col K j) $ i = 0"
proof-
  show  "j < n \<Longrightarrow> i < m \<Longrightarrow> fst (\<E>s ! j) \<noteq> snd (\<E>s ! j) \<Longrightarrow> \<N>s ! i = fst (\<E>s ! j) \<Longrightarrow> col K j $ i = 1"
    by simp
next
  show " j < n \<Longrightarrow> i < m \<Longrightarrow> fst (\<E>s ! j) \<noteq> snd (\<E>s ! j) \<Longrightarrow> \<N>s ! i = snd (\<E>s ! j) \<Longrightarrow> col K j $ i = - 1"
    by auto
next
  show " j < n \<Longrightarrow> i < m \<Longrightarrow> \<N>s ! i \<noteq> fst (\<E>s ! j) \<Longrightarrow> \<N>s ! i \<noteq> snd (\<E>s ! j) \<Longrightarrow> col K j $ i = 0 "
    by auto
qed

lemma K_col_list_map_elem: "j < n \<Longrightarrow> i < m  \<Longrightarrow> 
    col K j $ i = map_vec (\<lambda> x . if (x = fst (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else if (x = snd (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0) (vec_of_list \<N>s) $ i"
  using incidence_mat_col_list_map_elem no_self_loop nth_mem by (simp add: vec_of_list_index)

lemma K_col_list_map: "j < n \<Longrightarrow> col K j = map_vec (\<lambda> x . if (x =fst (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else  if (x = snd (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0) (vec_of_list \<N>s)"
  using K_col_list_map_elem  by (simp add: vec_eq_iff)

lemma K_row_def: "j < n \<Longrightarrow> i < m \<Longrightarrow> (row K i) $ j = (if (\<N>s!i) = fst (\<E>s!j) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else if (\<N>s!i) = snd (\<E>s!j)  \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0)"
 using incidence_matrix_row_def 
  by (simp add: network_wf)

lemma K_row_def_indiv: "j < n \<Longrightarrow> i < m \<Longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j) \<Longrightarrow> (\<N>s!i) = fst (\<E>s!j) \<Longrightarrow> (row K i) $ j = 1"
     "j < n \<Longrightarrow> i < m  \<Longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j) \<Longrightarrow> (\<N>s!i) = snd (\<E>s!j) \<Longrightarrow> (row K i) $ j = -1"
     "j < n \<Longrightarrow> i < m \<Longrightarrow> (\<N>s!i) \<noteq> fst (\<E>s!j) \<Longrightarrow>  (\<N>s!i) \<noteq> snd (\<E>s!j) \<Longrightarrow> (row K i) $ j = 0"
  by(simp_all add: K_matrix_pos_iff K_matrix_zero_iff  K_matrix_neg_iff)


text \<open>Alternate positive - negative oriented edge representations \<close>

lemma pos_edges_mat_cond_rep:
  assumes "j < length \<E>s" and "fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)"
  shows " fst (\<E>s ! j) \<in> ((!) \<N>s) ` { i. i < length \<N>s \<and> K $$ (i, j) = 1}"
  by (smt (verit, best) K_matrix_pos_iff assms imageI mem_Collect_eq nth_mem valid_nodes_index_obtains wf_network_system wf_network_system_iff)

lemma neg_edges_mat_cond_rep:
  assumes "j < length \<E>s" and "fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)"
  shows "snd (\<E>s ! j) \<in> ((!) \<N>s) ` { i. i < length \<N>s \<and> K $$ (i, j) = -1}"
  by (smt (verit, best) K_matrix_neg_iff assms imageI mem_Collect_eq nth_mem valid_nodes_index_obtains wf_network_system wf_network_system_iff)

lemma no_incidence_edge_mat_cond_rep:
 assumes "j < length \<E>s" and "fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)"
 shows " fst (\<E>s ! j) \<notin> ((!) \<N>s) ` { i. i < length \<N>s \<and> K $$ (i, j) = 0}" "snd (\<E>s ! j) \<notin> ((!) \<N>s) ` { i. i < length \<N>s \<and> K $$ (i, j) = 0}"
proof-
  show "fst (\<E>s ! j) \<notin> (!) \<N>s ` {i. i < m \<and> K $$ (i, j) = 0}"
    using assms K_matrix_zero_iff wf_network_system by fastforce
  show "snd (\<E>s ! j) \<notin> (!) \<N>s ` {i. i < m \<and> K $$ (i, j) = 0} "
    using K_matrix_neg_iff assms by force
qed


lemma mat_degree_num_K_row: 
  assumes "i < m"
  shows "mat_degree_num K i = sum_abs_vec (row K i)"
  by (simp add: K_elems assms mat_degree_property)


end

end