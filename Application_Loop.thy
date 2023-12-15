theory Application_Loop
imports Loop_Matrix
begin 


context nonempty_loop_system
begin


lemma loop_matrix_rlc: 
  fixes \<N>s :: "'a nodes" and \<E>s :: "'a edges" and \<L>s :: "'a edges list"
  assumes nodes: "\<N>s = [n1::'a, n2, n3, n4]" and edges: "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
   and loops: "\<L>s = [[(n4,n1),(n1,n2),(n2,n4)], [(n3,n4),(n4,n2),(n2,n3)], [(n4,n1), (n1,n3), (n3,n4)], [(n4,n1),(n1,n2),(n2,n3),(n3,n4)], 
                     [(n4,n1),(n1,n3),(n3,n4)],[(n2,n1),(n1,n3),(n3,n4),(n4,n2)], [(n4,n1),(n1,n3),(n3,n2),(n2,n4)]]"  
 shows "(C :: real mat)  = mat_of_rows_list 6 [[1::real, 1, 0, 0, 1, 0],[0::real, 0, 0, -1, -1, 1], [1::real, 0, 1, 0, 0, 1], [1::real, 1, 0, -1, 0, 1],
                                               [1::real, 0, 1, 0, 0, 1], [0::real, -1, 1, 0, -1, 1], [1::real, 0, 1, 1, 1, 0]]"  (is "_ = ?rhs")
proof(rule eq_matI)
  have 0: "distinct \<N>s" 
    by (simp add: distincts(1))
  have 1: "C \<in> carrier_mat 7 6" 
    using assms C_carrier_mat by (simp add: numeral_eq_Suc)
  then have 2: "dim_col C = 6" by auto
  then have 3: "dim_row C = 7" using 1 by auto
  have 4: "dim_row ?rhs = 7"
    by (simp add: mat_of_rows_list_def)
  have 5: "dim_col ?rhs = 6"
    by (simp add: mat_of_rows_list_def)
  have 6: "n1 \<noteq> n2" "n1 \<noteq> n3"  "n1 \<noteq> n4" "n2 \<noteq> n3" "n2 \<noteq> n4" "n3 \<noteq>  n4" using 0 assms by simp+
  have pos00: "in_pos_loop (\<E>s!0) (\<L>s!0)" 
    using assms 
    by (metis C_matrix_pos_iff edges_nempty in_pos_loop length_greater_0_conv list.set_intros(1) loop_list_nempty loop_matrix_one_pos_iff nth_Cons_0)
  have pos01: "in_pos_loop (\<E>s!1) (\<L>s!0)"   
  using assms in_pos_loop wellformed_1 0 
  by (metis "3" One_nat_def list.set_intros(1) list.set_intros(2) lloop_list nth_Cons_0 nth_Cons_Suc zero_less_numeral) 
  have pos04b: " (\<E>s!4) \<in> set (\<L>s!0)" using assms by auto
  then have pos04: "in_pos_loop (\<E>s!4) (\<L>s!0)" using assms in_pos_loop
    by (metis dim_row_is_l length_Cons less_Suc_eq list.size(3) lloop_list nth_mem numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
  have pos15b: "(\<E>s!5)\<in> set (\<L>s!1)"  using assms by auto
  then have pos15: "in_pos_loop (\<E>s!5) (\<L>s!1)"using assms in_pos_loop
    by (metis "2" "3" Suc_1 dim_col_C dim_row_is_l edges_nempty eval_nat_numeral(3) length_greater_0_conv lessI loop_set nat_add_left_cancel_less nth_mem numeral_3_eq_3 numeral_less_iff plus_1_eq_Suc semiring_norm(81) wellformed_1)
  have pos20b: "(\<E>s!0)\<in> set (\<L>s!2)"  using assms by auto
  then have pos20: "in_pos_loop (\<E>s!0) (\<L>s!2)" using assms in_pos_loop
    by (metis "6"(3) One_nat_def Suc_1 fst_conv in_loop_not_samepos_directed_cond_indexed length_Cons less_Suc_eq list.size(3) not_in_loop_indexed nth_Cons_0 snd_conv)
  have pos22b: "(\<E>s!2)\<in> set (\<L>s!2)"  using assms by auto
  then have pos22: "in_pos_loop (\<E>s!2) (\<L>s!2)" using assms in_pos_loop 
    by (metis One_nat_def Suc_1 dim_row_is_l length_Cons less_Suc_eq list.size(3) lloop_list nth_mem)
  have pos25b: "(\<E>s!5)\<in> set (\<L>s!2)"  using assms by auto
  then have pos25: "in_pos_loop (\<E>s!5) (\<L>s!2)" using assms in_pos_loop 
    by (metis dim_row_is_l length_Cons less_Suc_eq list.size(3) lloop_list nth_mem numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) pred_numeral_simps(3) semiring_norm(26) semiring_norm(27))
  have pos30b: "(\<E>s!0)\<in> set (\<L>s!3)"  using assms by auto
  then have pos30: "in_pos_loop (\<E>s!0) (\<L>s!3)" using assms in_pos_loop
    by (metis "2" "3" "6"(3) dim_col_C dim_row_is_l fst_conv in_loop_not_samepos_directed_cond_indexed not_in_loop_indexed nth_Cons_0 numeral_less_iff semiring_norm(77) semiring_norm(80) snd_conv zero_less_numeral)
  have pos31b: "(\<E>s!1) \<in> set (\<L>s!3)"  using assms by auto
  then have pos31: "in_pos_loop (\<E>s!1) (\<L>s!3)" using assms in_pos_loop
    by (metis "2" "3" "6"(1) One_nat_def diff_Suc_1 dim_col_C dim_row_is_l fst_eqD in_loop_not_samepos_directed_cond_indexed not_in_loop_indexed nth_Cons_0 nth_Cons_numeral 
              numeral_less_iff numerals(1) semiring_norm(76) semiring_norm(77) semiring_norm(80) snd_eqD)
  have pos35b: "(\<E>s!5) \<in> set (\<L>s!3)"  using assms by auto
  then have pos35: "in_pos_loop (\<E>s!5) (\<L>s!3)" using assms in_pos_loop 
     by (metis C_matrix_pos_iff dim_col_C dim_row_is_l inpos_loop_C_one length_Cons less_Suc_eq list.size(3) numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) pred_numeral_simps(3) semiring_norm(26) semiring_norm(27))
  have pos40b: "(\<E>s!0) \<in> set (\<L>s!4)"  using assms by auto
  then have pos40: "in_pos_loop (\<E>s!0) (\<L>s!4)" using assms in_pos_loop 
      by (metis "2" "3" "6"(3) dim_col_C dim_row_is_l eval_nat_numeral(2) eval_nat_numeral(3) fst_conv in_loop_not_samepos_directed_cond_indexed less_Suc_eq not_in_loop_indexed nth_Cons_0 semiring_norm(28) snd_conv zero_less_numeral)
  have pos42b: "(\<E>s!2) \<in> set (\<L>s!4)"  using assms by auto
  then have pos42: "in_pos_loop (\<E>s!2) (\<L>s!4)" using assms in_pos_loop 
     by (metis "2" "3" "6"(2) One_nat_def Suc_1 Suc_le_mono diff_Suc_1 dim_col_C dim_row_is_l fst_eqD in_loop_not_samepos_directed_cond_indexed not_in_loop_indexed 
        nth_Cons_0 nth_Cons_numeral numeral_3_eq_3 numeral_le_iff numeral_less_iff numerals(1) semiring_norm(77) semiring_norm(78) semiring_norm(79) snd_eqD zero_less_one_class.zero_le_one)
  have pos45b: "(\<E>s!5) \<in> set (\<L>s!4)"  using assms by auto
  then have pos45: "in_pos_loop (\<E>s!5) (\<L>s!4)" using assms in_pos_loop 
     by (metis "2" "3" One_nat_def Suc_1 Suc_le_mono dim_col_C dim_row_is_l eval_nat_numeral(2) lessI linordered_nonzero_semiring_class.zero_le_one C_matrix_edge_in_revloop 
         inneg_loop_C_mone  not_in_loop_indexed numeral_3_eq_3 numeral_le_iff numeral_less_iff semiring_norm(28) semiring_norm(79))
  have pos52b: "(\<E>s!2) \<in> set (\<L>s!5)"  using assms by auto
  then have pos52: "in_pos_loop (\<E>s!2) (\<L>s!5)" using assms in_pos_loop 
     by (metis dim_row_is_l length_Cons less_Suc_eq list.size(3) lloop_list nth_mem numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) pred_numeral_simps(3) semiring_norm(26) semiring_norm(27))
  have pos55b: "(\<E>s!5) \<in> set (\<L>s!5)"  using assms by auto
  then have pos55: "in_pos_loop (\<E>s!5) (\<L>s!5)" using assms in_pos_loop 
     by (metis "2" "3" BitM_plus_one One_nat_def Suc_1 Suc_numeral dim_col_C dim_row_is_l lessI C_matrix_edge_in_revloop inneg_loop_C_mone not_in_loop_indexed numeral_3_eq_3 numeral_less_iff semiring_norm(28) semiring_norm(80))
  have pos60b: "(\<E>s!0) \<in> set (\<L>s!6)"  using assms by auto
  then have pos60: "in_pos_loop (\<E>s!0) (\<L>s!6)" using assms in_pos_loop 
     by (metis "2" "3" "6"(3) dim_col_C dim_row_is_l eval_nat_numeral(3) fst_conv in_loop_not_samepos_directed_cond_indexed lessI not_in_loop_indexed nth_Cons_0 snd_conv zero_less_numeral)
  have pos62b: "(\<E>s!2) \<in> set (\<L>s!6)"  using assms by auto
  then have pos62: "in_pos_loop (\<E>s!2) (\<L>s!6)" using assms in_pos_loop 
     by (metis "2" "3" One_nat_def Suc_1 Suc_le_mono dim_col_C dim_row_is_l eval_nat_numeral(2) eval_nat_numeral(3) lessI lloop_list not_numeral_le_zero nth_mem semiring_norm(28) verit_comp_simplify1(3))
  have pos63b: "(\<E>s!3) \<in> set (\<L>s!6)"  using assms by auto
  then have pos63: "in_pos_loop (\<E>s!3) (\<L>s!6)" using assms in_pos_loop 
     by (metis "2" dim_col_C dim_row_is_l length_Cons less_Suc_eq list.size(3) lloop_list nth_mem numeral_3_eq_3)
  have pos64b: "(\<E>s!4) \<in> set (\<L>s!6)"  using assms by auto
  then have pos64: "in_pos_loop (\<E>s!4) (\<L>s!6)" using assms in_pos_loop 
     by (metis "2" dim_col_C dim_row_is_l length_Cons less_Suc_eq list.size(3) lloop_list nth_mem numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
  have neg13b:" (reverse (\<L>s!1)) = [(n3,n2),(n2,n4),(n4,n3)]" using assms by(simp add: reverse_def)
  then have "(\<E>s!3)\<in> set (reverse (\<L>s!1))" using assms by auto   
  then have neg13: "in_neg_loop (\<E>s!3) (\<L>s!1)"
    using assms in_neg_loop 2 3 edge_rloop1 
    by (metis dim_col_C dim_row_is_l loop_rev_set nth_mem numeral_less_iff numerals(1) semiring_norm(77) semiring_norm(81) wellformed_1)
  have neg14b: "(\<E>s!4)\<in> set (reverse (\<L>s!1))" using assms by auto   
  then have neg14: "in_neg_loop (\<E>s!4) (\<L>s!1)" 
    using assms in_neg_loop 2 3 edge_rloop1 
    by (metis Suc_1 Suc_less_eq dim_col_C dim_row_is_l edges_nempty eval_nat_numeral(3) length_greater_0_conv lessI loop_rev_set nth_mem numeral_3_eq_3 numeral_less_iff semiring_norm(78) wellformed_1)
  have neg33b: "(\<E>s!3)\<in> set (reverse (\<L>s!3))" using assms by auto
  then have neg33: "in_neg_loop (\<E>s!3) (\<L>s!3)" 
    using assms in_neg_loop 2 3 edge_rloop1
    by (metis length_Cons less_Suc_eq list.size(3) loop_rev_set neg_loop_cond_indexed numeral_3_eq_3 valid_loops_index wellformed_1) 
  have neg51b: "(\<E>s!1)\<in> set (reverse (\<L>s!5))" using assms by auto
  then have neg51: "in_neg_loop (\<E>s!1) (\<L>s!5)" 
    using assms in_neg_loop 2 3 edge_rloop1
    by (metis One_nat_def Suc_1 dim_col_C dim_row_is_l lessI in_loop_not_oppositeneg_directed wf_pos_loop  not_in_loop_indexed nth_mem numeral_3_eq_3 numeral_One numeral_less_iff semiring_norm(76) semiring_norm(80) wf_loop_system)
  have neg54b: "(\<E>s!4)\<in> set (reverse (\<L>s!5))" using assms by auto
  then have neg54: "in_neg_loop (\<E>s!4) (\<L>s!5)" 
    using assms in_neg_loop 2 3 edge_rloop1
    by (metis dim_col_C dim_row_is_l less_Suc_eq loop_rev_set neg_loop_cond_indexed numeral_eq_Suc pred_numeral_simps(2) pred_numeral_simps(3) semiring_norm(28) valid_loops_index wellformed_1)
  have no02b: "(\<E>s!2) \<notin> set (\<L>s!0) \<and> (\<E>s!2)\<notin> set (reverse (\<L>s!0))"
    using assms 6 by auto
  then have no02:  "\<not>in_neg_loop (\<E>s!2) (\<L>s!0) \<and> \<not> in_pos_loop (\<E>s!2) (\<L>s!0)"
    using assms wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no03b: " (\<E>s!3) \<notin> set (\<L>s!0) \<and> (\<E>s!3)\<notin> set (reverse (\<L>s!0))"
    using assms 6  by auto
  then have no03:  "\<not>in_neg_loop (\<E>s!3) (\<L>s!0) \<and> \<not> in_pos_loop (\<E>s!3) (\<L>s!0)"
    using assms  wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no05b: " (\<E>s!5) \<notin> set (\<L>s!0) \<and> (\<E>s!5)\<notin> set (reverse (\<L>s!0))"
    using assms 6  by auto
  then have no05:  "\<not>in_neg_loop (\<E>s!5) (\<L>s!0) \<and> \<not> in_pos_loop (\<E>s!5) (\<L>s!0)"
    using assms  wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no10b: " (\<E>s!0) \<notin> set (\<L>s!1) \<and> (\<E>s!0)\<notin> set (reverse (\<L>s!1))"
    using assms 6  by auto
  then have no10:  "\<not>in_neg_loop (\<E>s!0) (\<L>s!1) \<and> \<not> in_pos_loop (\<E>s!0) (\<L>s!1)"
    using assms wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no11b: " (\<E>s!1) \<notin> set (\<L>s!1) \<and> (\<E>s!1)\<notin> set (reverse (\<L>s!1))"
    using assms 6  by auto
  then have no11:  "\<not>in_neg_loop (\<E>s!1) (\<L>s!1) \<and> \<not> in_pos_loop (\<E>s!1) (\<L>s!1)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no12b: " (\<E>s!2) \<notin> set (\<L>s!1) \<and> (\<E>s!2)\<notin> set (reverse (\<L>s!1))"
    using assms 6  by auto
  then have no12:  "\<not>in_neg_loop (\<E>s!2) (\<L>s!1) \<and> \<not> in_pos_loop (\<E>s!2) (\<L>s!1)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no21b: " (\<E>s!1) \<notin> set (\<L>s!2) \<and> (\<E>s!1)\<notin> set (reverse (\<L>s!2))"
    using assms 6 by auto
  then have no21:  "\<not>in_neg_loop (\<E>s!1) (\<L>s!2) \<and> \<not> in_pos_loop (\<E>s!1) (\<L>s!2)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no23b: " (\<E>s!3) \<notin> set (\<L>s!2) \<and> (\<E>s!3) \<notin> set (reverse (\<L>s!2))"
    using assms 6 by auto
  then have no23:  "\<not>in_neg_loop (\<E>s!3) (\<L>s!2) \<and> \<not> in_pos_loop (\<E>s!3) (\<L>s!2)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no24b: " (\<E>s!4) \<notin> set (\<L>s!2) \<and> (\<E>s!4) \<notin> set (reverse (\<L>s!2))"
    using assms 6 by auto
  then have no24:  "\<not>in_neg_loop (\<E>s!4) (\<L>s!2) \<and> \<not> in_pos_loop (\<E>s!4) (\<L>s!2)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no32b: " (\<E>s!2) \<notin> set (\<L>s!3) \<and> (\<E>s!2) \<notin> set (reverse (\<L>s!3))"
    using assms 6 by auto
  then have no32:  "\<not>in_neg_loop (\<E>s!2) (\<L>s!3) \<and> \<not> in_pos_loop (\<E>s!2) (\<L>s!3)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no34b: " (\<E>s!4) \<notin> set (\<L>s!3) \<and> (\<E>s!4) \<notin> set (reverse (\<L>s!3))"
    using assms 6 by auto
  then have no34:  "\<not>in_neg_loop (\<E>s!4) (\<L>s!3) \<and> \<not> in_pos_loop (\<E>s!4) (\<L>s!3)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
 have no41b: " (\<E>s!1) \<notin> set (\<L>s!4) \<and> (\<E>s!1) \<notin> set (reverse (\<L>s!4))"
    using assms 6 by auto
  then have no41:  "\<not>in_neg_loop (\<E>s!1) (\<L>s!4) \<and> \<not> in_pos_loop (\<E>s!1) (\<L>s!4)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
 have no43b: " (\<E>s!3) \<notin> set (\<L>s!4) \<and> (\<E>s!3) \<notin> set (reverse (\<L>s!4))"
    using assms 6 by auto
 then have no43:  "\<not>in_neg_loop (\<E>s!3) (\<L>s!4) \<and> \<not> in_pos_loop (\<E>s!3) (\<L>s!4)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
 have no44b: " (\<E>s!4) \<notin> set (\<L>s!4) \<and> (\<E>s!4) \<notin> set (reverse (\<L>s!4))"
    using assms 6 by auto
 then have no44:  "\<not>in_neg_loop (\<E>s!4) (\<L>s!4) \<and> \<not> in_pos_loop (\<E>s!4) (\<L>s!4)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
 have no50b: " (\<E>s!0) \<notin> set (\<L>s!5) \<and> (\<E>s!0) \<notin> set (reverse (\<L>s!5))"
    using assms 6 by auto
 then have no50:  "\<not>in_neg_loop (\<E>s!0) (\<L>s!5) \<and> \<not> in_pos_loop (\<E>s!0) (\<L>s!5)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
 have no53b: " (\<E>s!3) \<notin> set (\<L>s!5) \<and> (\<E>s!3) \<notin> set (reverse (\<L>s!5))"
    using assms 6 by auto
 then have no53:  "\<not>in_neg_loop (\<E>s!3) (\<L>s!5) \<and> \<not> in_pos_loop (\<E>s!3) (\<L>s!5)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
 have no61b: " (\<E>s!1) \<notin> set (\<L>s!6) \<and> (\<E>s!1) \<notin> set (reverse (\<L>s!6))"
    using assms 6 by auto
 then have no61:  "\<not>in_neg_loop (\<E>s!1) (\<L>s!6) \<and> \<not> in_pos_loop (\<E>s!1) (\<L>s!6)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
 have no65b: " (\<E>s!5) \<notin> set (\<L>s!6) \<and> (\<E>s!5) \<notin> set (reverse (\<L>s!6))"
    using assms 6 by auto
 then have no65:  "\<not>in_neg_loop (\<E>s!5) (\<L>s!6) \<and> \<not> in_pos_loop (\<E>s!5) (\<L>s!6)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
 show c1: "dim_row C = dim_row ?rhs"
    using 3 4 by auto
 show c2: "dim_col C = dim_col ?rhs"
    using 2 5 by auto
 show " \<And>i j. i < dim_row ?rhs \<Longrightarrow>
           j < dim_col ?rhs \<Longrightarrow> C $$ (i, j) = ?rhs $$ (i, j)"
 proof-
  fix i j  assume i: "i<dim_row ?rhs" and j: "j < dim_col ?rhs "
  have "C$$ (0,0) = ?rhs $$ (0,0)"
    using i j pos00 inpos_loop_C_one c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover  have "C$$ (0,1) = ?rhs $$ (0,1)"
    using i j pos01 inpos_loop_C_one c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (0,2) = ?rhs $$ (0,2)"
    using i j no02 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (0,3) = ?rhs $$ (0,3)"
    using i j no03 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (0,4) = ?rhs $$ (0,4)"
    using i j pos04 inpos_loop_C_one c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (0,5) = ?rhs $$ (0,5)"
    using i j no05 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,0) = ?rhs $$ (1,0)"
    using i j no10 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,1) = ?rhs $$ (1,1)"
    using i j no11 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,2) = ?rhs $$ (1,2)"
    using i j no12 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,3) = ?rhs $$ (1,3)"
    using i j neg13 inneg_loop_C_mone c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,4) = ?rhs $$ (1,4)"
    using i j neg14 inneg_loop_C_mone c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover  have "C$$ (1,5) = ?rhs $$ (1,5)"
    using i j pos15 inpos_loop_C_one c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover  have "C$$ (2,0) = ?rhs $$ (2,0)"
    using i j pos20 inpos_loop_C_one c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,1) = ?rhs $$ (2,1)"
    using i j no21 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,2) = ?rhs $$ (2,2)"
    using i j pos22 inpos_loop_C_one  c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,3) = ?rhs $$ (2,3)"
    using i j no23 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,4) = ?rhs $$ (2,4)"
    using i j no24 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,5) = ?rhs $$ (2,5)"
    using i j pos25 inpos_loop_C_one  c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (3,0) = ?rhs $$ (3,0)"
    using i j pos30 inpos_loop_C_one  c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (3,1) = ?rhs $$ (3,1)"
    using i j pos31 inpos_loop_C_one  c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (3,2) = ?rhs $$ (3,2)"
    using i j no32 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (3,3) = ?rhs $$ (3,3)"
    using i j neg33 inneg_loop_C_mone c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (3,4) = ?rhs $$ (3,4)"
    using i j no34 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (3,5) = ?rhs $$ (3,5)"
    using i j pos35 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (4,0) = ?rhs $$ (4,0)"
    using i j pos40 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (4,1) = ?rhs $$ (4,1)"
    using i j no41 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (4,2) = ?rhs $$ (4,2)"
    using i j pos42 inpos_loop_C_one c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (4,3) = ?rhs $$ (4,3)"
    using i j no43 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (4,4) = ?rhs $$ (4,4)"
    using i j no44 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (4,5) = ?rhs $$ (4,5)"
    using i j pos45 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (5,0) = ?rhs $$ (5,0)"
    using i j no50 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (5,1) = ?rhs $$ (5,1)"
    using i j neg51 inneg_loop_C_mone c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (5,2) = ?rhs $$ (5,2)"
    using i j pos52 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (5,3) = ?rhs $$ (5,3)"
    using i j no53 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (5,4) = ?rhs $$ (5,4)"
    using i j neg54 inneg_loop_C_mone c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (5,5) = ?rhs $$ (5,5)"
    using i j pos55 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (6,0) = ?rhs $$ (6,0)"
    using i j pos60 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (6,1) = ?rhs $$ (6,1)"
    using i j no61 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (6,2) = ?rhs $$ (6,2)"
    using i j pos62 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (6,3) = ?rhs $$ (6,3)"
    using i j pos63 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def) 
  moreover have "C$$ (6,4) = ?rhs $$ (6,4)"
    using i j pos64 inpos_loop_C_one c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (6,5) = ?rhs $$ (6,5)"
    using i j no65 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  ultimately have  "C$$ (i,j) = ?rhs $$ (i,j)"
    using i j c1 c2 assms 6 1 2 3 4 5
    by (smt (verit) Suc_eq_numeral Suc_lessI dim_col_C dim_row_is_l length_Cons length_greater_0_conv 
          less_2_cases lloop_list loop_matrix_pos no05 not_inloop_C_zero not_less_eq numeral_3_eq_3 one_less_numeral_iff 
            pos15b pred_numeral_simps(2) pred_numeral_simps(3) semiring_norm(26) semiring_norm(27) semiring_norm(76))
  then show "C$$ (i,j) = ?rhs $$ (i,j)" by auto
  qed
qed






end
end
