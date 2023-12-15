theory Application_Incidence
imports Incidence_Matrix
begin 

context nonempty_network_system

begin 



text\<open>Example of Figure 1: Let a network associated linear graph with 4 nodes and 6 edges and the coefficient matrix 
of Kirchhoff's current law equations\<close>  


lemma nonempty_network_sys_given_network: 
  fixes Ns :: "'a nodes" and Es :: "'a edges" assumes dist : "distinct Ns "
  assumes nodes: "Ns = [n1::'a, n2, n3, n4]" and edges: "Es = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
  shows "nonempty_network_system Ns Es"
proof
  show c1: "distinct Ns" using dist by simp
  have a1: "n1 \<noteq> n2" "n2 \<noteq> n3" "n1 \<noteq> n3" "n1 \<noteq> n4" "n2 \<noteq> n4" using c1 nodes by auto
  show c2: "distinct Es" using a1 edges nodes by auto
  show "Es \<noteq> []" using edges by auto
  show "\<And>e. e \<in> set Es \<Longrightarrow> fst e \<in> set Ns \<and> snd e \<in> set Ns \<and> fst e \<noteq> snd e "
    using assms by auto
qed


lemma incidence_matrix_rlc: 
  fixes \<N>s :: "'a nodes" and \<E>s :: "'a edges"
  assumes nodes: "\<N>s = [n1::'a, n2, n3, n4]" and edges: "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
  shows "K  = mat_of_rows_list 6 [[-1::real, 1, 1, 0 , 0, 0], [0::real, -1, 0, -1, 1, 0],
                                [0::real, 0, -1, 1, 0, 1], [1::real, 0, 0, 0, -1, -1]] " (is "_=?rhs")  
proof(rule eq_matI)
  have 0: "nonempty_network_system \<N>s \<E>s" using assms wf_nonempty_netw_list_sys by blast
  then have 1: "distinct \<N>s" using assms distincts(1) by auto
  then have 2: "distinct \<E>s" using assms distincts(2) by auto
  have 3: "K = (incidence_matrix [n1::'a, n2, n3, n4] [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)] ::real mat)"
    using assms by meson
  then have 4: "K \<in> carrier_mat 4 6" using assms K_carrier_mat by auto
  then have 5: "dim_row K = 4"  using dim_row_K by auto
  then have 6: "dim_col K = 6"  using 4 dim_col_K by auto
  have posincs: "pos_incident (\<N>s!0) (\<E>s!1)" "pos_incident (\<N>s!0) (\<E>s!2)" "pos_incident (\<N>s!1) (\<E>s!4)"
                "pos_incident (\<N>s!2) (\<E>s!3)" "pos_incident (\<N>s!2) (\<E>s!5)"  "pos_incident (\<N>s!3) (\<E>s!0)" 
    using assms pos_incident_netw_altdef 1 by auto
  have negincs: "neg_incident (\<N>s!0) (\<E>s!0)"  "neg_incident (\<N>s!1) (\<E>s!1)"  "neg_incident (\<N>s!1) (\<E>s!3)" 
                 "neg_incident (\<N>s!2) (\<E>s!2)"  "neg_incident (\<N>s!3) (\<E>s!4)"  "neg_incident (\<N>s!3) (\<E>s!5)" 
    using assms neg_incident_netw_altdef 1 by auto 
  have notincs: "\<not> pos_incident (\<N>s!1) (\<E>s!0) \<and> \<not> neg_incident (\<N>s!1) (\<E>s!0)" "\<not> pos_incident (\<N>s!0) (\<E>s!3) \<and> \<not> neg_incident (\<N>s!0) (\<E>s!3)" 
      "\<not> pos_incident (\<N>s!0) (\<E>s!4) \<and> \<not> neg_incident (\<N>s!0) (\<E>s!4)" "\<not> pos_incident (\<N>s!0) (\<E>s!5) \<and> \<not> neg_incident (\<N>s!0) (\<E>s!5)"
     "\<not> pos_incident (\<N>s!1) (\<E>s!2) \<and> \<not> neg_incident (\<N>s!1) (\<E>s!2)" "\<not> pos_incident (\<N>s!1) (\<E>s!5) \<and> \<not> neg_incident (\<N>s!1) (\<E>s!5)"
      "\<not> pos_incident (\<N>s!2) (\<E>s!0) \<and> \<not> neg_incident (\<N>s!2) (\<E>s!0)" "\<not> pos_incident (\<N>s!2) (\<E>s!1) \<and> \<not> neg_incident (\<N>s!2) (\<E>s!1)"
      "\<not> pos_incident (\<N>s!2) (\<E>s!4) \<and> \<not> neg_incident (\<N>s!2) (\<E>s!4)" "\<not> pos_incident (\<N>s!3) (\<E>s!1) \<and> \<not> neg_incident (\<N>s!3) (\<E>s!1)" 
      "\<not> pos_incident (\<N>s!3) (\<E>s!2) \<and> \<not> neg_incident (\<N>s!3) (\<E>s!2)" "\<not> pos_incident (\<N>s!3) (\<E>s!3) \<and> \<not> neg_incident (\<N>s!3) (\<E>s!3)" 
    using assms not_pos_not_neg_incident_netw 1 by auto
  show c1: "dim_col K = dim_col ?rhs" using assms 6 by auto
  show c2: "dim_row K = dim_row ?rhs" using assms 5 by auto
  show c3: "\<And>i j. i < dim_row (?rhs) \<Longrightarrow> j < dim_col (?rhs) \<Longrightarrow> K $$ (i, j) = ?rhs $$ (i, j) "  
  proof-
    fix i j assume i: "i < dim_row (?rhs)" and j: " j < dim_col (?rhs)"
    have r00: "K $$ (0, 0) = ?rhs $$ (0, 0)"
      using negincs(1) neg_inc_K_mone 
      by (smt (verit) "5" "6" mat_of_rows_list_def c2 index_mat(1) matrl_carrier(2) nth_Cons_0 old.prod.case zero_less_numeral)
    then have r01: "K $$ (0, 1) = ?rhs $$ (0, 1)"
      using i j posincs(1) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    then have r02: "K $$ (0, 2) = ?rhs $$ (0, 2)"
      using i j posincs(2) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    then have r03: "K $$ (0, 3) = ?rhs $$ (0, 3)"
       using i j notincs(2) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)      
    then have r04: "K $$ (0, 4) = ?rhs $$ (0, 4)"
       using i j notincs(3) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)      
    then have r05: "K $$ (0, 5) = ?rhs $$ (0, 5)"
       using i j notincs(4) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def) 
    then have r10: "K $$ (1, 0) = ?rhs $$ (1, 0)" 
       using i j notincs(1) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)    
    then have r11: "K $$ (1, 1) = ?rhs $$ (1, 1)"    
      using i j negincs(2) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def) 
    then have r12: "K $$ (1, 2) = ?rhs $$ (1, 2)" 
       using i j notincs(5) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)   
    then have r13: "K $$ (1, 3) = ?rhs $$ (1, 3)" 
       using i j negincs(3) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def) 
    then have r14: "K $$ (1, 4) = ?rhs $$ (1, 4)" 
       using i j posincs(3) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    then have r15: "K $$ (1, 5) = ?rhs $$ (1, 5)" 
       using i j notincs(6) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def) 
    then have r20: "K $$ (2, 0) = ?rhs $$ (2, 0)" 
       using i j notincs(7) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def) 
    then have r21: "K $$ (2, 1) = ?rhs $$ (2, 1)" 
       using i j notincs(8) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def) 
    then have r22: "K $$ (2, 2) = ?rhs $$ (2, 2)"
      using i j negincs(4) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def)
    then have r23: "K $$ (2, 3) = ?rhs $$ (2, 3)" 
      using i j posincs(4) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    then have r24: "K $$ (2, 4) = ?rhs $$ (2, 4)"  
      using i j notincs(9) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)
    then have r25: "K $$ (2, 5) = ?rhs $$ (2, 5)" 
      using i j posincs(5) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    then have r30: "K $$ (3, 0) = ?rhs $$ (3, 0)" 
      using i j posincs(6) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    then have r31: "K $$ (3, 1) = ?rhs $$ (3, 1)"
      using i j notincs(10) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)   
    then have r32: "K $$ (3, 2) = ?rhs $$ (3, 2)" 
      using i j notincs(11) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)
    then have r33: "K $$ (3, 3) = ?rhs $$ (3, 3)"
      using i j notincs(12) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)
    then have r34: "K $$ (3, 4) = ?rhs $$ (3, 4)"
      using i j negincs(5) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def)
    then have r35: "K $$ (3, 5) = ?rhs $$ (3, 5)"
      using i j negincs(6) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def)
    then show " K $$ (i, j) = ?rhs $$ (i, j)"
      using r34 r33 r32 r31 r30 r25 r24 r23 r22 r21 r20 r15 r14 r13 r12 r11 r10 r05 r04 r03 r02 r01 r00 i j
      by (smt (z3) "5" One_nat_def assms(1) assms(2) c1 c2 dim_col_K dim_row_K eval_nat_numeral(3) length_Cons less_Suc_eq less_one list.size(3) numeral_2_eq_2)
  qed
qed






















end
end