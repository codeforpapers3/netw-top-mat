theory Loop_Matrix
 imports Network_Loop_System
          Incidence_Matrix 
          
begin


subsection \<open>Loop Vector\<close>

context nonempty_loop_system
begin


definition loop_vec :: "'a edges list \<Rightarrow> 'a edge \<Rightarrow> ('b :: {field_char_0}) vec" where
"loop_vec Ls p \<equiv> vec (length Ls) (\<lambda>k. 
      if p \<in> set (reverse (loop_list (Ls!k))) \<and> p \<notin> set (loop_list (Ls!k)) then -1
        else if p \<in> set (loop_list (Ls!k)) then 1 else 0)"


lemma loop_cvec_elems: "set\<^sub>v (loop_vec Ls p) \<subseteq> {0, 1, -1}"
by (auto simp add: vec_set_def loop_vec_def)

lemma finite_loop_cvec_elems: "finite (set\<^sub>v (loop_vec Ls p))"
using finite_subset loop_cvec_elems by blast

lemma loop_cvec_dim: "dim_vec (loop_vec Ls p) = length Ls" by (simp add: loop_vec_def)

lemma loop_cvec_index: "k < length Ls \<Longrightarrow> loop_vec Ls p $ k = (if p \<in> set (reverse (loop_list (Ls!k))) \<and> p \<notin> set (loop_list (Ls!k)) then -1
        else if p \<in> set (loop_list (Ls!k)) then 1  else 0)"
by(simp add: loop_vec_def)

lemma loop_cvec_index_mone: "k < length Ls \<Longrightarrow>  loop_vec Ls p $ k = -1 \<longleftrightarrow> p \<in> set (reverse (loop_list (Ls!k))) \<and> p \<notin> set (loop_list (Ls!k))"
by(simp add: loop_vec_def)

lemma loop_cvec_index_one: "k < length Ls  \<Longrightarrow>  p \<notin> set (reverse (loop_list (Ls!k))) \<Longrightarrow> loop_vec Ls p $ k = 1 \<longleftrightarrow> p \<in> set (loop_list (Ls!k))"
by(simp add: loop_vec_def)

lemma loop_cvec_index_zero: "k < length Ls \<Longrightarrow> loop_vec Ls p $ k = 0 \<longleftrightarrow> p \<notin> set (loop_list (Ls!k)) \<and> p \<notin> set (reverse (loop_list (Ls!k)))"
  by(simp add: loop_vec_def)


subsection \<open>Loop Row Vector\<close>

definition loop_row_vec :: "'a edges  \<Rightarrow> 'a edges  \<Rightarrow> ('b :: {field_char_0}) vec" where
"loop_row_vec L Es \<equiv> vec (length Es) (\<lambda>j. if (Es!j) \<in> set (reverse (loop_list L)) \<and> (Es!j) \<notin> set (loop_list L) then -1
 else if (Es!j) \<in> set (loop_list L) then 1 else 0)"

lemma loop_rvec_elems: "set\<^sub>v (loop_row_vec L Es) \<subseteq> {0, 1, -1}"
  by (auto simp add: vec_set_def loop_row_vec_def)

lemma finite_loop_rvec_elems: "finite (set\<^sub>v (loop_row_vec L Es))"
  using finite_subset loop_rvec_elems by blast

lemma loop_rvec_dim: "dim_vec (loop_row_vec L Es) = length Es" by (simp add: loop_row_vec_def)

lemma loop_rvec_index: "j < length Es \<Longrightarrow> loop_row_vec L Es $ j= (if (Es!j) \<in> set (reverse (loop_list L)) \<and> (Es!j) \<notin> set (loop_list  L) then -1
 else if (Es!j) \<in> set (loop_list L) then 1 else 0)"
  by(simp add: loop_row_vec_def)

lemma loop_rvec_index_mone: "j < length Es  \<Longrightarrow> (Es!j) \<notin> set (loop_list L) \<Longrightarrow> loop_row_vec L Es $ j = -1  \<longleftrightarrow> (Es!j) \<in> set (reverse (loop_list L))"
  by(simp add: loop_row_vec_def)

lemma loop_rvec_index_one: "j < length Es \<Longrightarrow>  loop_row_vec L Es $ j = 1 \<longleftrightarrow> (Es!j) \<in> set (loop_list L)"
  by(simp add: loop_row_vec_def)

lemma loop_rvec_index_zero: "j < length Es \<Longrightarrow> loop_row_vec L Es $ j = 0 \<longleftrightarrow> (Es!j) \<notin> set (reverse (loop_list L)) \<and> (Es!j) \<notin> set (loop_list L)"
  by(simp add: loop_row_vec_def)

subsection \<open>Loop Matrix whose elements are  0, 1,and  -1\<close>

definition loop_matrix :: "'a edges list \<Rightarrow> 'a edges  \<Rightarrow> ('b :: {field_char_0}) mat" where
"loop_matrix Ls Es  \<equiv>  mat (length Ls) (length Es) 
(\<lambda>(k,j). if (Es!j) \<in> set (reverse (loop_list (Ls!k))) \<and> (Es!j) \<notin> set (loop_list (Ls!k)) then -1 else 
if (Es!j) \<in> set (loop_list (Ls!k)) then 1 else 0)"

lemma loop_matcol_dim: "dim_col (loop_matrix Ls Es) = length Es"   by (simp add: loop_matrix_def)
lemma loop_matrow_dim: "dim_row (loop_matrix Ls Es) = length Ls" by (simp add: loop_matrix_def)

lemma loop_mat_elems: "elements_mat (loop_matrix Ls Es) \<subseteq> {0, 1, -1}"
by (auto simp add: elements_mat_def loop_matrix_def)

lemma finite_loop_mat_elems: "finite (elements_mat (loop_matrix Ls Es))"
using finite_subset loop_mat_elems by blast

lemma loop_index[simp]: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
loop_matrix Ls Es  = mat (length Ls) (length Es) (\<lambda>(k,j). if (Es!j) \<in> set (reverse (loop_list (Ls!k))) \<and> (Es!j) \<notin> set (loop_list (Ls!k))  then -1 else 
if (Es!j) \<in> set (loop_list (Ls!k)) then 1 else 0)"
unfolding loop_matrix_def by blast

lemma loop_carrier[simp]: "loop_matrix Ls Es \<in> carrier_mat (length Ls) (length Es)" 
  unfolding carrier_mat_def by (auto simp add: loop_matcol_dim loop_matrow_dim)

lemma loop_matrix_pos: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (Es!j) \<in> set (loop_list (Ls!k))
    \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 1"
    unfolding loop_matrix_def by auto

lemma loop_matrix_neg:  "k < length Ls \<Longrightarrow> j < length Es  \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow> (Es!j) \<in> set (reverse (loop_list (Ls!k)))
    \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = -1"
  unfolding loop_matrix_def by auto    

lemma loop_matrix_0: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow> (Es!j) \<notin> set (reverse (loop_list (Ls!k)))
    \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 0"
  by(simp add: loop_matrix_def)

lemma loop_matrix_one_pos: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 1
    \<Longrightarrow> (Es!j) \<in> set (loop_list (Ls!k))"
  by (metis loop_matrix_0 loop_matrix_neg one_neq_neg_one zero_neq_one)

lemma loop_matrix_mone_neg: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = -1
    \<Longrightarrow> (Es!j) \<in> set (reverse (loop_list (Ls!k)))"
  by (metis loop_matrix_0 loop_matrix_pos one_neq_neg_one zero_neq_neg_one)

lemma loop_matrix_zero_no: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 0
    \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow>  (Es!j) \<notin> set (reverse (loop_list (Ls!k)))"
  by (metis loop_matrix_neg zero_neq_neg_one)

lemma loop_matrix_one_pos_iff:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 1  \<longleftrightarrow> (Es!j) \<in> set (loop_list (Ls!k))"
  using loop_matrix_pos loop_matrix_one_pos by metis

lemma loop_matrix_mone_neg_iff:  "k < length Ls \<Longrightarrow> j < length Es  \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = -1  \<longleftrightarrow> (Es!j) \<in> set (reverse (loop_list (Ls!k)))"
  using loop_matrix_neg loop_matrix_mone_neg by auto

lemma loop_matrix_zero_no_iff:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 0  \<longleftrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<and> (Es!j) \<notin> set (reverse (loop_list (Ls!k)))"
   using loop_matrix_0 by auto

lemma loop_matrix_mone_implies: "H \<subseteq> {..<length Ls} \<Longrightarrow> j < length Es \<Longrightarrow> 
    (\<And> k. k\<in>H \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = -1) \<Longrightarrow> k \<in> H \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k))  \<Longrightarrow> (Es!j) \<in> set (reverse (loop_list (Ls!k)))"
  using loop_matrix_mone_neg_iff by blast

lemma loop_matrix_one_implies: "H \<subseteq> {..<length Ls} \<Longrightarrow> j < length Es \<Longrightarrow> 
    (\<And> k. k\<in>H \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 1) \<Longrightarrow> k \<in> H \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow> (Es!j) \<notin> set (reverse (loop_list (Ls!k)))  \<Longrightarrow> (Es!j) \<in> set (loop_list (Ls!k))"
  using loop_matrix_one_pos_iff by blast

lemma loop_matrix_zero_implies: "H \<subseteq> {..<length Ls} \<Longrightarrow> j < length Es \<Longrightarrow> 
    (\<And> k. k\<in>H \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 0) \<Longrightarrow> k \<in> H \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow> (Es!j) \<notin> set (reverse (loop_list (Ls!k)))"
  using loop_matrix_zero_no_iff by blast


text \<open>Reasoning on Columns/Rows of the loop matrix\<close>

lemma loop_matrix_col_def:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
(col (loop_matrix Ls Es) j) $ k = (if (Es!j) \<in> set (reverse (loop_list (Ls!k))) \<and> (Es!j) \<notin> set (loop_list (Ls!k)) then -1 else if (Es!j) \<in> set (loop_list (Ls!k)) then 1 else 0)"
  by (simp add: loop_matrix_def)

lemma loop_matrix_col_list_map_elem:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
(col (loop_matrix Ls Es) j) $ k =  map_vec 
    (\<lambda> X . if (Es!j) \<in> set (reverse (loop_list X)) \<and> (Es!j) \<notin> set (loop_list X) then -1 else if (Es!j) \<in> set (loop_list X) then 1 else 0) (vec_of_list Ls) $ k"
  by (simp add: loop_matrix_col_def vec_of_list_index)

lemma loop_mat_col_list_map:  "j < length Es \<Longrightarrow> 
    col (loop_matrix Ls Es) j = map_vec (\<lambda> X. if (Es!j) \<in> set (reverse (loop_list X)) \<and> (Es!j) \<notin> set (loop_list X) then -1 else if (Es!j) \<in> set (loop_list X) then 1 else 0) (vec_of_list Ls)"
by (intro eq_vecI,
    simp_all add: loop_matcol_dim loop_matrow_dim loop_matrix_col_list_map_elem index_vec_of_list loop_matrix_def)

lemma loop_matrix_row_def:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
(row (loop_matrix Ls Es) k) $ j = (if (Es!j) \<in> set (reverse (loop_list (Ls!k))) \<and> (Es!j) \<notin> set (loop_list (Ls!k)) then -1 else if (Es!j) \<in> set (loop_list (Ls!k)) then 1 else 0)"
  by (simp add: loop_matrix_def)

lemma loop_matrix_row_list_map_elem:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
(row (loop_matrix Ls Es) k) $ j = map_vec 
    (\<lambda> y. if y \<in> set (reverse (loop_list (Ls!k))) \<and> y \<notin>  set (loop_list (Ls!k))
 then -1 else if y \<in>  set (loop_list (Ls!k)) then 1 else 0) (vec_of_list Es) $ j"
  by (simp add: loop_matrix_row_def vec_of_list_index)


lemma loop_matrix_row_map:  "k < length Ls \<Longrightarrow>
row (loop_matrix Ls Es) k = map_vec 
    (\<lambda> y. if  y \<in> set (reverse (loop_list (Ls!k))) \<and> y \<notin>  set (loop_list (Ls!k))
 then -1 else if y \<in> set (loop_list (Ls!k)) then 1 else 0) (vec_of_list Es) "
proof(intro eq_vecI)
  show "\<And>i. k < length Ls \<Longrightarrow>
         i < dim_vec (map_vec (\<lambda>y. if y \<in> set (reverse (loop_list (Ls ! k))) \<and> y \<notin> set (loop_list (Ls ! k)) then - 1 else if y \<in> set (loop_list (Ls ! k)) then 1 else 0) (vec_of_list Es)) \<Longrightarrow>
         row (loop_matrix Ls Es) k $ i = map_vec (\<lambda>y. if y \<in> set (reverse (loop_list (Ls ! k))) \<and> y \<notin> set (loop_list (Ls ! k)) then - 1 else if y \<in> set (loop_list (Ls ! k)) then 1 else 0) (vec_of_list Es) $ i "
    using loop_matrix_row_def  by (simp add: vec_of_list_alt)
  show " k < length Ls \<Longrightarrow> dim_vec (row (loop_matrix Ls Es) k) = dim_vec (map_vec (\<lambda>y. if y \<in> set (reverse (loop_list (Ls ! k))) \<and> y \<notin> set (loop_list (Ls ! k)) then - 1 else if y \<in> set (loop_list (Ls ! k)) then 1 else 0) (vec_of_list Es))"
    by (simp add: loop_matcol_dim)
qed



text \<open>Connection between the loop vectors and the loop matrix\<close>

lemma loop_colmat_loop_vec: " j < length Es \<Longrightarrow>  col (loop_matrix Ls Es) j = loop_vec Ls (Es ! j)"
  by (auto simp add: loop_matrix_def loop_vec_def)

lemma loop_colsmat_loop_vecs: 
  assumes "\<forall>j \<in> {0..< length Es}. fst (Es!j) \<noteq> snd (Es!j)"
  shows "cols (loop_matrix Ls Es) = map (\<lambda> j. loop_vec Ls j) Es"
proof (intro nth_equalityI)
  have l1: "length (cols (loop_matrix Ls Es)) = length Es"
    using loop_matcol_dim by simp
  have l2: "length (map (\<lambda> j .loop_vec Ls j) Es) = length Es"
    using length_map by simp
  then show "length (cols (loop_matrix Ls Es)) = length (map (loop_vec Ls) Es)" 
    using l1 l2 by simp
  show "\<And>i. i < length (cols (loop_matrix Ls Es)) \<Longrightarrow> cols (loop_matrix Ls Es) ! i = map (loop_vec Ls) Es ! i "
    by (simp add:loop_matcol_dim loop_colmat_loop_vec)
qed

lemma loop_rowmat_loop_rowvec: " k < length Ls \<Longrightarrow> row (loop_matrix Ls Es) k = loop_row_vec (Ls!k) Es"
   by (auto simp add: loop_matrix_def loop_row_vec_def) 

lemma loop_rowsmat_loop_rowvecs: 
  shows "rows (loop_matrix Ls Es) = map (\<lambda> k. loop_row_vec k Es) Ls"
  by (smt (verit, best) length_rows loop_matrow_dim loop_rowmat_loop_rowvec map_nth_eq_conv nth_rows)

text \<open>Define a real-valued loop matrix represents the nonempty loop system \<close>

abbreviation C :: "real mat" where
"C \<equiv> loop_matrix \<L>s \<E>s"

lemma C_alt_def: "C = mat l n (\<lambda> (k,j). if in_neg_loop (\<E>s!j) (\<L>s!k) then -1 else if in_pos_loop (\<E>s!j) (\<L>s!k) then 1 else 0)"
  unfolding loop_matrix_def using neg_loop_altdef in_pos_loop 
  by (simp add: cong_mat)
 

lemma inpos_loop_C_one: "k < dim_row C \<Longrightarrow> j < dim_col C \<Longrightarrow> in_pos_loop (\<E>s!j) (\<L>s!k) \<longleftrightarrow> C $$ (k,j) = 1"
  using C_alt_def pos_loop_altdef 
  by (metis (mono_tags, opaque_lifting) in_pos_loop loop_matcol_dim loop_matrix_one_pos_iff loop_matrow_dim nth_mem)
 
lemma inneg_loop_C_mone: "k < dim_row C \<Longrightarrow> j < dim_col C \<Longrightarrow> in_neg_loop (\<E>s!j) (\<L>s!k) \<longleftrightarrow> C $$ (k,j) = -1"
  using C_alt_def neg_loop_altdef by simp

lemma not_inloop_C_zero: "k < dim_row C \<Longrightarrow> j < dim_col C \<Longrightarrow> \<not> in_neg_loop (\<E>s!j) (\<L>s!k)
                             \<Longrightarrow> \<not> in_pos_loop (\<E>s!j) (\<L>s!k) \<Longrightarrow> C $$ (k,j) = 0"
  by (simp add: C_alt_def)
lemma not_inloop_C_zero1: assumes "k < dim_row C" "j < dim_col C "
  shows "\<not> in_neg_loop (\<E>s!j) (\<L>s!k)
                             \<and>  \<not> in_pos_loop (\<E>s!j) (\<L>s!k) \<longleftrightarrow> C $$ (k,j) = 0"
  using assms 
  by (metis inneg_loop_C_mone inpos_loop_C_one not_inloop_C_zero one_neq_zero zero_neq_neg_one)


lemma lloop_list: "k < dim_row C \<Longrightarrow> (\<L>s!k) = loop_list (\<L>s!k)" 
  using loop_list_def wellformed_1  by (simp add: loop_matrow_dim)
 
text \<open>Matrix Dimension related lemmas \<close>
 
lemma C_carrier_mat: "C \<in> carrier_mat l n" 
  by (simp add: loop_matrix_def)

lemma dim_row_is_l[simp]: "dim_row C = l"
  using C_carrier_mat by blast

lemma dim_col_C[simp]: "dim_col C = n"
   using loop_matcol_dim by blast 

lemma dim_vec_row_C: "dim_vec (row C k) = n"
  by simp

lemma dim_vec_col_C: "dim_vec (col C k) = l"
  by simp 

lemma dim_vec_C_col: 
  assumes "j < n"
  shows "dim_vec (cols C ! j) = l"
  using assms by simp

lemma C_elems: "elements_mat (C) \<subseteq> {0, 1, -1}"
  by (auto simp add: loop_matrix_def elements_mat_def)

text \<open>Transpose properties \<close>

lemma transpose_C_mult_dim: "dim_row (C * C\<^sup>T) = l" "dim_col (C * C\<^sup>T) = l"
  by (simp_all)

lemma C_trans_index_val: "k < dim_col C \<Longrightarrow> j < dim_row C \<Longrightarrow> 
    C\<^sup>T $$ (k, j) = (if (in_neg_loop (\<E>s!k) (\<L>s!j)) then -1 else if (in_pos_loop (\<E>s!k) (\<L>s!j)) then 1 else 0)"
  using C_alt_def by force

lemma C_trans_index_val_alt: " k < dim_col C \<Longrightarrow> j < dim_row C \<Longrightarrow> 
    C\<^sup>T $$ (k, j) = (if (\<E>s!k) \<in> set (reverse (loop_list (\<L>s!j))) \<and> (\<E>s!k) \<notin> set (loop_list (\<L>s!j)) then -1 else if 
 (\<E>s!k) \<in> set (loop_list (\<L>s!j)) then 1 else 0)"
  using C_trans_index_val by(simp add: loop_matrix_def)
                           
lemma transpose_entries: "elements_mat (C\<^sup>T) \<subseteq> {0, 1, -1}"
  using C_trans_index_val elements_matD 
  by (metis index_transpose_mat(2) index_transpose_mat(3) insertCI subsetI)

text \<open>Loop Matrix elements and index related lemmas \<close>

lemma C_mat_row_elems: "k < l \<Longrightarrow> vec_set (row C k) \<subseteq> {0, 1, -1}"
  by (metis C_elems dim_row_is_l row_elems_subset_mat subset_trans)

lemma C_mat_col_elems: "j < n \<Longrightarrow> vec_set (col C j) \<subseteq> {0, 1, -1}"
  by (metis C_elems col_elems_subset_mat dim_col_C subset_trans)

lemma C_matrix_elems_one_mone_zero: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 0 \<or> C $$ (k, j) = 1 \<or> C $$ (k, j) = -1" 
  by (simp add: loop_matrix_def)

lemma C_not_zero_simp: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> C $$ (k, j) \<noteq> 0 \<Longrightarrow> C $$ (k, j) = 1 \<or> C $$ (k, j) = -1"
  using loop_mat_elems[of "\<L>s" "\<E>s"] by blast

lemma C_not_one_simp: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> C $$ (k, j) \<noteq> 1 \<Longrightarrow> C $$ (k, j) = 0 \<or> C $$ (k, j) = -1"
  using incidence_mat_elems[of "\<N>s" "\<E>s"] by auto

lemma C_not_mone_simp: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> C $$ (k, j) \<noteq> -1 \<Longrightarrow> C $$ (k, j) = 0 \<or> C $$ (k, j) = 1"
  using incidence_mat_elems[of "\<N>s" "\<E>s"] by fastforce

lemma C_not_Mone_simp: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> C $$ (k, j) \<noteq> 1 \<Longrightarrow> C $$ (k, j) \<noteq> -1 \<Longrightarrow> C $$ (k, j) = 0"
  using C_not_mone_simp  by blast

lemma C_index_square_itself: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> (C $$ (k, j))^2 = abs (C $$ (k, j))"
  using C_not_zero_simp by simp

lemma C_row_index_square_itself: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> ((row C k) $ j)^2 = abs ((row C k) $ j)"
  using index_row  C_index_square_itself by auto 

lemma C_matrix_edge_in_revloop: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = -1 \<Longrightarrow>  (\<E>s ! j) \<notin>  set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k))"
  using loop_matrix_mone_neg
  by (metis filter_True loop_matrix_one_pos_iff loop_list_def nth_mem one_neq_neg_one wellformed_1) 

lemma tC_dimcol_is_K_dimcol: "dim_col K = dim_row C\<^sup>T"
  by simp

lemma dimrow_tC_K: "dim_row (K * C\<^sup>T) = m"
   using dim_row_K 
   by (metis index_mult_mat(2))

lemma dimcol_tC_K: "dim_col (K * C\<^sup>T) = l"
  by simp

lemma C_matrix_edge_in_loop: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 1 \<Longrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k)"
  using loop_matrix_one_pos
 by (metis loop_list_alt nth_mem)

lemma C_matrix_edge_notin_loop: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 0 \<Longrightarrow> (\<E>s ! j) \<notin>  set (\<L>s ! k) \<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k))"
  using loop_matrix_zero_no_iff
  by (metis neg_loop_altdef not_in_loop_indexed nth_mem pos_loop_altdef) 

lemma C_matrix_edge_notin_loop': "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 0 \<longleftrightarrow> ((\<E>s ! j) \<notin>  set (\<L>s ! k) \<and> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k))) \<or> ((\<E>s ! j) \<in>  set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k)))"
  by (metis lloop_list loop_matrix_zero_no_iff loop_matrow_dim nth_mem wf_2)
  

lemma C_matrix_pos_iff: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 1 \<longleftrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k) "
  using C_matrix_edge_in_loop
  by (meson loop_list_alt loop_matrix_one_pos_iff nth_mem wellformed_1 wf_network_system wf_network_system_iff) 

lemma C_matrix_neg_iff: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = -1 \<longleftrightarrow> (\<E>s ! j) \<notin> set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k))"
  by (meson C_matrix_edge_in_loop C_matrix_edge_in_revloop C_matrix_edge_notin_loop C_matrix_elems_one_mone_zero)

lemma C_matrix_zero_iff: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 0 \<longleftrightarrow> (\<E>s ! j) \<notin>  set ((\<L>s ! k)) \<and> (\<E>s ! j) \<notin> set (reverse ((\<L>s ! k)))"
  by (metis C_matrix_edge_in_revloop C_matrix_edge_notin_loop C_matrix_elems_one_mone_zero C_matrix_pos_iff zero_neq_one)

text \<open>Loop Vector is a column of the loop matrix\<close>

lemma col_loop_vec: "j < length \<E>s \<Longrightarrow> loop_vec \<L>s (\<E>s ! j) = col C j"
  by (simp add: loop_colmat_loop_vec) 

text \<open>Loop row vector is equal to the row of the loop matrix\<close>

lemma row_loop_vec: "k < length \<L>s \<Longrightarrow> loop_row_vec (\<L>s!k) \<E>s = row C k"
  by (simp add: loop_rowmat_loop_rowvec)

text \<open>Loop matrix column properties\<close>

lemma C_col_def: "j < n \<Longrightarrow> k < l \<Longrightarrow> (col C j) $ k = (if (\<E>s ! j) \<notin> set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k))  then -1 
  else if (\<E>s ! j) \<in> set ((\<L>s ! k)) then 1 else 0)"
  using loop_matrix_col_def C_alt_def 
  by (smt (verit, best) C_matrix_neg_iff C_matrix_pos_iff col_mat index_mat(1) index_vec)

lemma C_col_def_indiv: "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<in> set (reverse (\<L>s ! k)) \<Longrightarrow> (\<E>s ! j) \<notin> set (\<L>s ! k) \<Longrightarrow> (col C j) $ k = -1"
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k) \<Longrightarrow> (col C j) $ k = 1"
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k)) \<Longrightarrow> (\<E>s ! j) \<notin> set (\<L>s ! k) \<Longrightarrow> (col C j) $ k = 0"
  using C_col_def by presburger+

lemma C_col_list_map_elem: "j < n \<Longrightarrow> k < l \<Longrightarrow> 
    col C j $ k = map_vec (\<lambda> X . if (\<E>s ! j) \<notin> set X \<and> (\<E>s!j) \<in> set (reverse X) then -1 else if (\<E>s ! j) \<in> set (X) then 1 else 0) (vec_of_list \<L>s) $ k"
  by (smt (verit, best) C_col_def dim_vec_of_list index_map_vec(1) index_vec_of_list)

lemma C_row_def: "j < n \<Longrightarrow> k < l \<Longrightarrow> (row C k) $ j = (if (\<E>s ! j) \<notin> set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k))  then -1 
  else if (\<E>s ! j) \<in> set ((\<L>s ! k)) then 1 else 0)"
  using C_matrix_neg_iff C_matrix_pos_iff C_matrix_zero_iff by force

lemma C_row_def_indiv: "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<in> set (reverse (\<L>s ! k)) \<Longrightarrow> (\<E>s ! j) \<notin> set (\<L>s ! k) \<Longrightarrow> (row C k) $ j = -1"
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k) \<Longrightarrow> (row C k) $ j = 1"
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k)) \<Longrightarrow> (\<E>s ! j) \<notin> set (\<L>s ! k) \<Longrightarrow> (row C k) $ j = 0"
 using C_row_def by presburger+


text \<open>Dimensional Connection between the incidence and the loop matrices\<close>

lemma C_dimcol_is_K_dimcol: "dim_col K = dim_col C"
  using dim_col_K dim_col_C by presburger

lemma dimcol_is_K_tC: "dim_col K = dim_row C\<^sup>T"
  by simp

lemma dimrow_K_tC: "dim_row (K * C\<^sup>T) = m"
   using dim_row_K 
   by (metis index_mult_mat(2))

lemma dimcol_tCK: "dim_col (K * C\<^sup>T) = l"
  by simp


text \<open>Degree of a loop matrix with respect to each row is equal to the number of nonzero elements of each row\<close>

lemma loop_mat_degree: "k < length \<L>s \<Longrightarrow> of_nat (mat_degree_num C k) = sum_abs_vec (row C k)"
  unfolding mat_degree_num_def mat_in_degree_num_def  mat_out_degree_num_def 
  using count_abs_vec1_sum_non_zero_elems_alt C_alt_def C_mat_row_elems by auto


text \<open>Relationship between loop matrix and incidence matrix via orthogonality\<close>

lemma inciloop_orthogonality_case1:
  assumes i :"i < dim_row K" and j: "j < dim_row C"
  assumes a3: "\<forall>k < n. fst (\<E>s ! k) \<noteq>  \<N>s ! i \<and> snd (\<E>s ! k) \<noteq>  \<N>s ! i" 
  shows "(row K i) \<bullet> (row C j) = 0"
proof -
  have 1: "\<forall>k < n. (row K i)$ k = 0" using a3 i K_row_def_indiv(3) by (metis dim_row_K)
  have 2: "(row K i) \<bullet> (row C j) = (\<Sum> k \<in> {0..<n} . (row K i) $ k * (row C j) $ k)"
    using i j by(simp add: scalar_prod_def)
  then have 3: "... =  (\<Sum> k \<in> {0..<n} . 0 * (row C j) $ k)"  using 1 2 by simp
  then have 4: "... = (\<Sum> k \<in> {0..<n} . 0)" by simp
  thus ?thesis using 2 3 4 by auto
qed

lemma inciloop_orthogonality_case2:
  assumes i :"i < dim_row K" and j: "j < dim_row C"
  assumes a4: "\<forall>k < n. (\<E>s ! k) \<notin> set (reverse (loop_list (\<L>s ! j))) \<and> (\<E>s ! k) \<notin> set (loop_list (\<L>s ! j))"
  shows "(row K i) \<bullet> (row C j) = 0"
proof -
  have 1: "\<forall>k < n. (row C j)$ k = 0" using a4 j C_row_def_indiv(3) by auto
  have 2 : "(row K i) \<bullet> (row C j) = (\<Sum> k \<in> {0..<n} . (row K i) $ k * 0)" using i j 1 assms by (simp add:scalar_prod_def)
  then have "... =  (\<Sum> k \<in> {0..<n} . 0)" by simp
  thus ?thesis using 1 2 by auto
qed


lemma inciloop_orthogonality_case3:
  assumes i :"i < dim_row K" and j: "j < dim_row C"
  assumes a5: "\<forall>k < n. (\<E>s ! k) \<notin> set (reverse (loop_list (\<L>s ! j))) \<and> (\<E>s ! k) \<notin> set (loop_list (\<L>s ! j)) \<and> fst (\<E>s ! k) \<noteq>  \<N>s ! i \<and> snd (\<E>s ! k) \<noteq>  \<N>s ! i"
  shows "(row K i) \<bullet> (row C j) = 0"
proof -
  have 1: "\<forall>k < n. (row K i)$ k = 0 \<and> (row C j)$ k = 0" using i j a5 C_row_def_indiv(3) K_row_def_indiv(3)
    by (metis dim_row_K dim_row_is_l loop_rvec_index_zero row_loop_vec)
  have 2 : "(row K i) \<bullet> (row C j) = (\<Sum> k \<in> {0..<n} . 0 * 0)"
    using i j 1 assms by (simp add:scalar_prod_def)
  then have "... =  (\<Sum> k \<in> {0..<n} . 0)" by simp
  thus ?thesis using 1 2 by auto
qed



end
end