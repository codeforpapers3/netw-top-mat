theory Application_Cutset
imports Cutset_Matrix
begin


context nonempty_cutset_system
begin

lemma cutset_matrix_rlc:
  fixes \<N>s :: "'a nodes" and \<E>s :: "'a edges"
  assumes nodes: "\<N>s = [n1::'a, n2, n3, n4]" and edges: "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
    and cutsets:  " \<C>s=[[(n2,n4), (n3,n4),(n4,n1)], [(n1,n3), (n3,n2), (n3,n4)], [(n1,n3), (n2,n4), (n3,n2), (n4,n1)], 
                                  [(n1,n2),(n3,n2),(n2,n4)]]"
  assumes forN0: "cuts_sgraph \<N>s (cut_list [n1,n2,n3])"
  assumes forN1: "cuts_sgraph \<N>s (cut_list [n1,n2,n4])"
  assumes forN2: "cuts_sgraph \<N>s (cut_list [n1,n2])"  
  assumes forN3: "cuts_sgraph \<N>s (cut_list [n1,n3,n4])"
  shows "B  = mat_of_rows_list 6 [[-1::real, 0, 0, 0 , 1, 1], [0::real, 0, 1, -1, 0, -1],
                                [-1::real, 0, 1, -1, 1, 0], [0::real, 1, 0, 1, -1, 0]] " (is "_=?rhs")  
proof(standard)
 have 0: "distinct \<N>s" using assms distincts(1) by auto
 have 1: "B \<in> carrier_mat 4 6" 
    using assms B_carrier_mat by (simp add: numeral_eq_Suc)
  then have 2: "dim_col B = 6" by auto
  then have 3: "dim_row B = 4" using 1 by auto
  have 4: "dim_row ?rhs = 4"
    by (simp add: mat_of_rows_list_def)
  have 5: "dim_col ?rhs = 6"
    by (simp add: mat_of_rows_list_def)
  have 6: "n1 \<noteq> n2" "n1 \<noteq> n3"  "n1 \<noteq> n4" "n2 \<noteq> n3" "n2 \<noteq> n4" "n3 \<noteq> n4" using 0 assms by simp+ 
  have N0: "N !0 = [n1, n2, n3]" using nodes 6 by(simp add: proper_sub_list_def) 
  have N1: "N !1 = [n1, n2, n4]" using nodes 6 by(simp add: proper_sub_list_def) 
  have N2: "N !2 = [n1, n2]" using nodes 6 by(simp add: proper_sub_list_def) 
  have N3: "N !3 = [n1, n3, n4]" using nodes 6 by(simp add: proper_sub_list_def)   
  have innegcut00: "in_neg_cutset (N!0) (\<E>s!0) (\<C>s!0)"
  proof-
     have "(\<C>s!0) \<in> set \<C>s" 
       using cutsets by auto
     moreover have "(\<E>s!0) \<in> set \<E>s" 
        using edges by simp
     moreover have "(\<E>s!0) \<in> set (\<C>s!0)" 
        using edges cutsets by auto    
     moreover have "snd (\<E>s!0) \<in> set (N!0)" 
        using edges N0 by simp
     moreover have "(\<E>s!0) \<in> set (neg_cut_list (N!0))" 
        using edges nodes N0 6 neg_cut_list_def[of "N!0"] by auto
     moreover have "(\<E>s!0) \<in> set (cutset (N!0))" 
        using N0 wf_2 nodes forN0 cut_list_pos_neg cut_list_def 
        by (metis calculation(5) filter_True negcut_is_cut nonempty_network_system.cutset_def wf_nonempty_netw_list_sys)
     ultimately have "in_neg_cutset (N!0) (\<E>s!0) (\<C>s!0)" using neg_cutset_altdef by auto
     thus ?thesis by auto
      qed
      have notpos00: "\<not> in_pos_cutset (N!0) (\<E>s!0) (\<C>s!0)"
        using innegcut00 pos_cut_not_neg pos_cutset_altdef neg_cutset_altdef by blast 
     have innegcut13: "in_neg_cutset (N!1) (\<E>s!3) (\<C>s!1)"
     proof-
      have "(\<C>s!1) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!3) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!3) \<in> set (\<C>s!1)" 
        using edges cutsets by auto    
      moreover have "snd (\<E>s!3) \<in> set (N!1)" 
        using edges N1 by simp
      moreover have "fst (\<E>s!3) \<in> set \<N>s - set (N!1)" 
        using edges nodes N1 6  by auto
      moreover have "(\<E>s!3) \<in> set (neg_cut_list (N!1))" 
        using edges nodes N1 6 neg_cut_list_def[of "N!1"] by auto
      moreover have "(\<E>s!3) \<in> set (cutset (N!1))" 
        using N1 wf_2 nodes forN1 cut_list_pos_neg cut_list_def 
        by (metis calculation(6) cutset_def filter_True negcut_is_cut)
        ultimately have "in_neg_cutset (N!1) (\<E>s!3) (\<C>s!1)" using neg_cutset_altdef by auto
      thus ?thesis by auto
    qed
    have notpos13: "\<not> in_pos_cutset (N!1) (\<E>s!3) (\<C>s!1)"       
      using innegcut13 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast
    have innegcut15: "in_neg_cutset (N!1) (\<E>s!5) (\<C>s!1)"
     proof-
      have "(\<C>s!1) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!5) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!5) \<in> set (\<C>s!1)" 
        using edges cutsets by auto    
      moreover have "snd (\<E>s!5) \<in> set (N!1)" 
        using edges N1 by simp
      moreover have "fst (\<E>s!5) \<in> set \<N>s - set (N!1)" 
        using edges nodes N1 6  by auto
      moreover have "(\<E>s!5) \<in> set (neg_cut_list (N!1))" 
        using edges nodes N1 6 neg_cut_list_def[of "N!1"] by auto
      moreover have "(\<E>s!5) \<in> set (cutset (N!1))" 
        using N1 wf_2 nodes forN1 cut_list_pos_neg cut_list_def 
        by (metis calculation(6) cuts_sgraph_def cutset_edges negcut_is_cut cutset_edges_iff)
        ultimately have "in_neg_cutset (N!1) (\<E>s!5) (\<C>s!1)" using neg_cutset_altdef by auto
      thus ?thesis by auto
    qed
    have notpos15: "\<not> in_pos_cutset (N!1) (\<E>s!5) (\<C>s!1)"       
      using innegcut15 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast
    have innegcut20: "in_neg_cutset (N!2) (\<E>s!0) (\<C>s!2)"
    proof-
      have "(\<C>s!2) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!0) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!0) \<in> set (\<C>s!2)" 
        using edges cutsets by auto    
      moreover have "snd (\<E>s!0) \<in> set (N!2)" 
        using edges N2 by simp
      moreover have "fst (\<E>s!0) \<in> set \<N>s - set (N!2)" 
        using edges nodes N2 6 by auto
      moreover have "(\<E>s!0) \<in> set (neg_cut_list (N!2))" 
        using edges nodes N2 6 neg_cut_list_def[of "N!2"] by auto
      moreover have "(\<E>s!0) \<in> set (cutset (N!2))" 
        using N2 wf_2 nodes forN2 wf_1 calculation(6) cutset_edges_iff negcut_is_cut 
        by (metis cutset_def filter_True)
        ultimately have "in_neg_cutset (N!2) (\<E>s!0) (\<C>s!2)" using neg_cutset_altdef by auto
      thus ?thesis by auto
     qed
      have notpos20: "\<not> in_pos_cutset (N!2) (\<E>s!0) (\<C>s!2)"       
        using innegcut20 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast
     have innegcut23: "in_neg_cutset (N!2) (\<E>s!3) (\<C>s!2)"
      proof-
      have "(\<C>s!2) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!3) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!3) \<in> set (\<C>s!2)" 
        using edges cutsets by auto    
      moreover have "snd (\<E>s!3) \<in> set (N!2)" 
        using edges N2 by simp
      moreover have "fst (\<E>s!3) \<in> set \<N>s - set (N!2)" 
        using edges nodes N2 6 by auto
      moreover have "(\<E>s!3) \<in> set (neg_cut_list (N!2))" 
        using edges nodes N2 6 neg_cut_list_def[of "N!2"] by auto
      moreover have "(\<E>s!3) \<in> set (cutset (N!2))" 
        using N2 wf_2 nodes forN2  wf_1
        calculation(6) cutset_edges_iff negcut_is_cut 
        by (metis cuts_sgraph_def cutset_edges)
        ultimately have "in_neg_cutset (N!2) (\<E>s!3) (\<C>s!2)" using neg_cutset_altdef by auto
      thus ?thesis by auto
      qed
     have notpos23: "\<not> in_pos_cutset (N!2) (\<E>s!3) (\<C>s!2)"       
        using innegcut23 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast 
      have innegcut34: "in_neg_cutset (N!3) (\<E>s!4) (\<C>s!3)"
      proof-
      have "(\<C>s!3) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!4) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!4) \<in> set (\<C>s!3)" 
        using edges cutsets by auto    
      moreover have "snd (\<E>s!4) \<in> set (N!3)" 
        using edges N3 by simp
      moreover have "fst (\<E>s!4) \<in> set \<N>s - set (N!3)" 
        using edges nodes N3 6 by auto
      moreover have "(\<E>s!4) \<in> set (neg_cut_list (N!3))" 
        using edges nodes N3 6 neg_cut_list_def[of "N!3"] by auto
      moreover have "(\<E>s!4) \<in> set (cutset (N!3))" 
        using N3 wf_2 nodes forN3 wf_1
        calculation(6) cutset_edges_iff negcut_is_cut 
        by (metis cutset_def filter_True)
        ultimately have "in_neg_cutset (N!3) (\<E>s!4) (\<C>s!3)" using neg_cutset_altdef by auto
      thus ?thesis by auto
    qed
      have notpos34: "\<not> in_pos_cutset (N!3) (\<E>s!4) (\<C>s!3)"       
        using innegcut34 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast 
      have inposcut04: "in_pos_cutset (N!0) (\<E>s!4) (\<C>s!0)"
      proof-
      have "(\<C>s!0) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!4) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!4) \<in> set (\<C>s!0)" 
        using edges cutsets by auto    
      moreover have "fst (\<E>s!4) \<in> set (N!0)" 
        using edges N0 by simp
      moreover have "snd (\<E>s!4) \<in> set \<N>s - set (N!0)" 
        using edges nodes N0 6  by auto
      moreover have "(\<E>s!4) \<in> set (pos_cut_list (N!0))" 
        using edges nodes N0 6 pos_cut_list_def by auto
      moreover have "(\<E>s!4) \<in> set (cutset (N!0))" 
        using N0 wf_2 nodes forN0 cut_list_pos_neg cut_list_def cutset_edges_iff poscut_is_cut 
        by (metis calculation(6) cuts_sgraph_def cutset_edges)
      ultimately have "in_pos_cutset (N!0) (\<E>s!4) (\<C>s!0)" 
        using pos_cutset_altdef pos_cutsetI by presburger
      thus ?thesis by auto
    qed
      have notneg04: "\<not> in_neg_cutset (N!0) (\<E>s!4) (\<C>s!0)"       
        using inposcut04 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast 
      have inposcut05: "in_pos_cutset (N!0) (\<E>s!5) (\<C>s!0)"
      proof-
      have "(\<C>s!0) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!5) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!5) \<in> set (\<C>s!0)" 
        using edges cutsets by auto    
      moreover have "fst (\<E>s!5) \<in> set (N!0)" 
        using edges N0 by simp
      moreover have "snd (\<E>s!5) \<in> set \<N>s - set (N!0)" 
        using edges nodes N0 6  by auto
      moreover have "(\<E>s!5) \<in> set (pos_cut_list (N!0))" 
        using edges nodes N0 6 pos_cut_list_def by auto
      moreover have "(\<E>s!5) \<in> set (cutset (N!0))" 
        using N0 wf_2 nodes forN0  cutset_edges_iff poscut_is_cut
        by (metis calculation(6) cuts_sgraph_def cutset_edges)
      ultimately have "in_pos_cutset (N!0) (\<E>s!5) (\<C>s!0)" 
        using pos_cutset_altdef pos_cutsetI by presburger
      thus ?thesis by auto
    qed
      have notneg05: "\<not> in_neg_cutset (N!0) (\<E>s!5) (\<C>s!0)"       
        using inposcut05 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast           
    have inposcut12: "in_pos_cutset (N!1) (\<E>s!2) (\<C>s!1)"
      proof-
      have "(\<C>s!1) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!2) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!2) \<in> set (\<C>s!1)" 
        using edges cutsets by auto    
      moreover have "fst (\<E>s!2) \<in> set (N!1)" 
        using edges N1 by simp
      moreover have "snd (\<E>s!2) \<in> set \<N>s - set (N!1)" 
        using edges nodes N1 6  by auto
      moreover have "(\<E>s!2) \<in> set (pos_cut_list (N!1))" 
        using edges nodes N1 6 pos_cut_list_def by auto
      moreover have "(\<E>s!2) \<in> set (cutset (N!1))" 
        using N1 wf_2 nodes forN1  cut_list_pos_neg cut_list_def 
        by (metis calculation(6) cutset_def cutset_edges filter_id_conv poscut_is_cut)
      ultimately have "in_pos_cutset (N!1) (\<E>s!2) (\<C>s!1)" 
        using pos_cutset_altdef pos_cutsetI by presburger
      thus ?thesis by auto
    qed
    have notneg12: "\<not> in_neg_cutset (N!1) (\<E>s!2) (\<C>s!1)"       
        using inposcut12 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast 
    have inposcut22: "in_pos_cutset (N!2) (\<E>s!2) (\<C>s!2)"
      proof-
      have "(\<C>s!2) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!2) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!2) \<in> set (\<C>s!2)" 
        using edges cutsets by auto    
      moreover have "fst (\<E>s!2) \<in> set (N!2)" 
        using edges N2 by simp
      moreover have "snd (\<E>s!2) \<in> set \<N>s - set (N!2)" 
        using edges nodes N2 6  by auto
      moreover have "(\<E>s!2) \<in> set (pos_cut_list (N!2))" 
        using edges nodes N2 6 pos_cut_list_def by auto
      moreover have "(\<E>s!2) \<in> set (cutset (N!2))" 
        using N2 wf_2 nodes forN2  cut_list_pos_neg cut_list_def
        by (metis calculation(6) cuts_sgraph_def cutset_edges cutset_edges_iff poscut_is_cut)
      ultimately have "in_pos_cutset (N!2) (\<E>s!2) (\<C>s!2)" 
        using pos_cutset_altdef pos_cutsetI by presburger
      thus ?thesis by auto
    qed
    have notneg22: "\<not> in_neg_cutset (N!2) (\<E>s!2) (\<C>s!2)"       
        using inposcut22 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast 
    have inposcut24: "in_pos_cutset (N!2) (\<E>s!4) (\<C>s!2)"
      proof-
      have "(\<C>s!2) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!4) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!4) \<in> set (\<C>s!2)" 
        using edges cutsets by auto    
      moreover have "fst (\<E>s!4) \<in> set (N!2)" 
        using edges N2 by simp
      moreover have "snd (\<E>s!4) \<in> set \<N>s - set (N!2)" 
        using edges nodes N2 6  by auto
      moreover have "(\<E>s!4) \<in> set (pos_cut_list (N!2))" 
        using edges nodes N2 6 pos_cut_list_def by auto
      moreover have "(\<E>s!4) \<in> set (cutset (N!2))" 
        using N2 wf_2 nodes forN2 cut_list_pos_neg cut_list_def
        by (metis calculation(6) cuts_sgraph_def cutset_edges cutset_edges_iff poscut_is_cut)
      ultimately have "in_pos_cutset (N!2) (\<E>s!4) (\<C>s!2)" 
        using pos_cutset_altdef pos_cutsetI by presburger
      thus ?thesis by auto
    qed
     have notneg24: "\<not> in_neg_cutset (N!2) (\<E>s!4) (\<C>s!2)"       
        using inposcut24 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast 
     have inposcut31: "in_pos_cutset (N!3) (\<E>s!1) (\<C>s!3)"
      proof-
      have "(\<C>s!3) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!1) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!1) \<in> set (\<C>s!3)" 
        using edges cutsets by auto    
      moreover have "fst (\<E>s!1) \<in> set (N!3)" 
        using edges N3 by simp
      moreover have "snd (\<E>s!1) \<in> set \<N>s - set (N!3)" 
        using edges nodes N3 6  by auto
      moreover have "(\<E>s!1) \<in> set (pos_cut_list (N!3))" 
        using edges nodes N3 6 pos_cut_list_def by auto
      moreover have "(\<E>s!1) \<in> set (cutset (N!3))" 
        using N3 wf_2 nodes forN3 cut_list_pos_neg cut_list_def
        using calculation(6) cutset_def by auto 
      ultimately have "in_pos_cutset (N!3) (\<E>s!1) (\<C>s!3)" 
        using pos_cutset_altdef pos_cutsetI by presburger
      thus ?thesis by auto
     qed
     have notneg31: "\<not> in_neg_cutset (N!3) (\<E>s!1) (\<C>s!3)"       
        using inposcut31 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast  
     have inposcut33: "in_pos_cutset (N!3) (\<E>s!3) (\<C>s!3)"
      proof-
      have "(\<C>s!3) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!3) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!3) \<in> set (\<C>s!3)" 
        using edges cutsets by auto    
      moreover have "fst (\<E>s!3) \<in> set (N!3)" 
        using edges N3 by simp
      moreover have "snd (\<E>s!3) \<in> set \<N>s - set (N!3)" 
        using edges nodes N3 6  by auto
      moreover have "(\<E>s!3) \<in> set (pos_cut_list (N!3))" 
        using edges nodes N3 6 pos_cut_list_def by auto
      moreover have "(\<E>s!3) \<in> set (cutset (N!3))" 
        using N3 wf_2 nodes forN3 cut_list_pos_neg cut_list_def 
        by (metis calculation(6) cutset_def filter_id_conv poscut_is_cut)
      ultimately have "in_pos_cutset (N!3) (\<E>s!3) (\<C>s!3)" 
        using pos_cutset_altdef pos_cutsetI by presburger
      thus ?thesis by auto
    qed
    have notneg33: "\<not> in_neg_cutset (N!3) (\<E>s!3) (\<C>s!3)"       
        using inposcut33 neg_cutset_altdef pos_cut_not_neg pos_cutset_altdef by blast  
   have notposnotneg01: "\<not> in_pos_cutset (N!0) (\<E>s!1) (\<C>s!0) \<and> \<not> in_neg_cutset (N!0) (\<E>s!1) (\<C>s!0)"
   proof-  
       have "(\<C>s!0) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!1) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!1) \<notin> set (\<C>s!0)" 
        using edges cutsets 6  by auto       
      ultimately have "\<not> in_pos_cutset (N!0) (\<E>s!1) (\<C>s!0) \<and> \<not> in_neg_cutset (N!0) (\<E>s!1) (\<C>s!0)" 
        using notin_cutsets_not_pos_not_neg by auto
      thus ?thesis by auto
    qed
   have notposnotneg02: "\<not> in_pos_cutset (N!0) (\<E>s!2) (\<C>s!0) \<and> \<not> in_neg_cutset (N!0) (\<E>s!2) (\<C>s!0)"
   proof-  
      have "(\<C>s!0) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!2) \<in> set \<E>s" 
        using edges by simp
      moreover have "(\<E>s!2) \<notin> set (\<C>s!0)" 
        using edges cutsets 6  by auto       
      ultimately have "\<not> in_pos_cutset (N!0) (\<E>s!2) (\<C>s!0) \<and> \<not> in_neg_cutset (N!0) (\<E>s!2) (\<C>s!0)" 
        using notin_cutsets_not_pos_not_neg by auto
      thus ?thesis by auto
    qed
    have notposnotneg03: "\<not> in_pos_cutset (N!0) (\<E>s!3) (\<C>s!0) \<and> \<not> in_neg_cutset (N!0) (\<E>s!3) (\<C>s!0)"
    proof-  
     have "(\<C>s!0) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!3) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!3) \<notin> set (\<C>s!0)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
    have notposnotneg10: "\<not> in_pos_cutset (N!1) (\<E>s!0) (\<C>s!1) \<and> \<not> in_neg_cutset (N!1) (\<E>s!0) (\<C>s!1)"
    proof-  
     have "(\<C>s!1) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!0) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!0) \<notin> set (\<C>s!1)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
    have notposnotneg11: "\<not> in_pos_cutset (N!1) (\<E>s!1) (\<C>s!1) \<and> \<not> in_neg_cutset (N!1) (\<E>s!1) (\<C>s!1)"
    proof-  
     have "(\<C>s!1) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!1) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!1) \<notin> set (\<C>s!1)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
    have notposnotneg14: "\<not> in_pos_cutset (N!1) (\<E>s!4) (\<C>s!1) \<and> \<not> in_neg_cutset (N!1) (\<E>s!4) (\<C>s!1)"
    proof-  
     have "(\<C>s!1) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!4) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!4) \<notin> set (\<C>s!1)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
    have notposnotneg21: "\<not> in_pos_cutset (N!2) (\<E>s!1) (\<C>s!2) \<and> \<not> in_neg_cutset (N!2) (\<E>s!1) (\<C>s!2)"
    proof-  
     have "(\<C>s!2) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!1) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!1) \<notin> set (\<C>s!2)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
   have notposnotneg25: "\<not> in_pos_cutset (N!2) (\<E>s!5) (\<C>s!2) \<and> \<not> in_neg_cutset (N!2) (\<E>s!5) (\<C>s!2)"
    proof-  
     have "(\<C>s!2) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!5) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!5) \<notin> set (\<C>s!2)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
    have notposnotneg30: "\<not> in_pos_cutset (N!3) (\<E>s!0) (\<C>s!3) \<and> \<not> in_neg_cutset (N!3) (\<E>s!0) (\<C>s!3)"
    proof-  
     have "(\<C>s!3) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!0) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!0) \<notin> set (\<C>s!3)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
 have notposnotneg32: "\<not> in_pos_cutset (N!3) (\<E>s!2) (\<C>s!3) \<and> \<not> in_neg_cutset (N!3) (\<E>s!2) (\<C>s!3)"
    proof-  
     have "(\<C>s!3) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!2) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!2) \<notin> set (\<C>s!3)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
    have notposnotneg35: "\<not> in_pos_cutset (N!3) (\<E>s!5) (\<C>s!3) \<and> \<not> in_neg_cutset (N!3) (\<E>s!5) (\<C>s!3)"
    proof-  
     have "(\<C>s!3) \<in> set \<C>s" 
        using cutsets by auto
      moreover have "(\<E>s!5) \<in> set \<E>s" 
        using edges by simp     
      moreover have "(\<E>s!5) \<notin> set (\<C>s!3)" 
        using edges cutsets 6  by auto       
       thus ?thesis  
        using notin_cutsets_not_pos_not_neg by blast
    qed
    show rdim: "dim_row B = dim_row ?rhs" using 3 4 by presburger
    show cdim: "dim_col B = dim_col ?rhs" using 2 5 by (simp add: mat_of_rows_list_def)
    show c3: "\<And>i j. i < dim_row (?rhs) \<Longrightarrow> j < dim_col (?rhs) \<Longrightarrow> B $$ (i, j) = ?rhs $$ (i, j)" 
  proof-
    fix i j assume i: "i < dim_row (?rhs)" and j: " j < dim_col (?rhs)"
    have r00: "B $$ (0, 0) = ?rhs $$ (0, 0)" 
      using i j innegcut00 notpos00 inneg_cuts_B_mone rdim cdim by (simp add: mat_of_rows_list_def) 
   moreover have r01: "B $$ (0, 1) = ?rhs $$ (0, 1)" 
      using i j notposnotneg01 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
  moreover have r02: "B $$ (0, 2) = ?rhs $$ (0, 2)" 
      using i j notposnotneg02 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r03: "B $$ (0, 3) = ?rhs $$ (0, 3)" 
      using i j notposnotneg03 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r04: "B $$ (0, 4) = ?rhs $$ (0, 4)" 
      using i j inposcut04 notneg04  inpos_cuts_B_one rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r05: "B $$ (0, 5) = ?rhs $$ (0, 5)" 
      using i j inposcut05 notneg05  inpos_cuts_B_one rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r10: "B $$ (1, 0) = ?rhs $$ (1, 0)" 
      using i j notposnotneg10 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r11: "B $$ (1, 1) = ?rhs $$ (1, 1)" 
      using i j notposnotneg11 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r12: "B $$ (1, 2) = ?rhs $$ (1, 2)" 
      using i j inposcut12 notneg12 inpos_cuts_B_one rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r13: "B $$ (1, 3) = ?rhs $$ (1, 3)" 
      using i j innegcut13 notpos13 inneg_cuts_B_mone rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r14: "B $$ (1, 4) = ?rhs $$ (1, 4)" 
      using i j notposnotneg14 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r15: "B $$ (1, 5) = ?rhs $$ (1, 5)" 
      using i j innegcut15 notpos15 inneg_cuts_B_mone rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r20: "B $$ (2, 0) = ?rhs $$ (2, 0)" 
      using i j innegcut20 notpos20 inneg_cuts_B_mone rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r21: "B $$ (2, 1) = ?rhs $$ (2, 1)" 
      using i j notposnotneg21 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r22: "B $$ (2, 2) = ?rhs $$ (2, 2)" 
      using i j inposcut22 notneg22 inpos_cuts_B_one rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r23: "B $$ (2, 3) = ?rhs $$ (2, 3)" 
      using i j innegcut23 notpos23 inneg_cuts_B_mone rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r24: "B $$ (2, 4) = ?rhs $$ (2, 4)" 
      using i j inposcut24 notneg24 inpos_cuts_B_one rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r25: "B $$ (2, 5) = ?rhs $$ (2, 5)" 
      using i j notposnotneg25 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r30: "B $$ (3, 0) = ?rhs $$ (3, 0)" 
      using i j notposnotneg30 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r31: "B $$ (3, 1) = ?rhs $$ (3, 1)" 
      using i j inposcut31 notneg31 inpos_cuts_B_one rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r32: "B $$ (3, 2) = ?rhs $$ (3, 2)" 
      using i j notposnotneg32 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r33: "B $$ (3, 3) = ?rhs $$ (3, 3)" 
      using i j inposcut33 notneg33 inpos_cuts_B_one rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r34: "B $$ (3, 4) = ?rhs $$ (3, 4)" 
      using i j innegcut34 notpos34 inneg_cuts_B_mone rdim cdim by (simp add: mat_of_rows_list_def)
    moreover have r35: "B $$ (3, 5) = ?rhs $$ (3, 5)" 
      using i j notposnotneg35 notin_cuts_B_zero rdim cdim by (simp add: mat_of_rows_list_def)
    ultimately have  "B$$ (i,j) = ?rhs $$ (i,j)"
    using i j rdim cdim 2 3 4 5 6 
     by (smt (verit) B_matrix_not_zero B_trans_index_val Suc_less_eq less_Suc_eq less_Suc_eq_0_disj 
         not_less_eq numeral_2_eq_2 numeral_eq_Suc numerals(1) one_less_numeral_iff pred_numeral_simps(2) 
          pred_numeral_simps(3) semiring_norm(26) semiring_norm(27) semiring_norm(28))
     then show "B$$ (i,j) = ?rhs $$ (i,j)" by auto
  qed
qed



end
end