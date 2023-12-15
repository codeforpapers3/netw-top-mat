theory Network_Incidence_System
  imports Main 

begin 

type_synonym 'a edge = "('a \<times> 'a)"
type_synonym 'a edges = "('a \<times> 'a) list"
type_synonym 'a node = "'a" 
type_synonym 'a nodes = "'a list"

section \<open> Network System\<close>
text \<open>We consider a network represented by a directed graph with no self-loops
 and multi-edges\<close>

locale network_system =
 fixes nodes_list:: "'a nodes" ("\<N>s") and  edges_list:: "'a edges" ("\<E>s")
  assumes network_wf: "e \<in> set \<E>s \<Longrightarrow> fst e \<in> set \<N>s \<and> snd e \<in> set \<N>s \<and> fst e \<noteq> snd e"
    and  distincts: "distinct \<N>s" "distinct \<E>s"
begin

abbreviation "m \<equiv> length \<N>s"
abbreviation "n \<equiv> length \<E>s"

abbreviation "\<N> \<equiv> set \<N>s"
abbreviation "\<E> \<equiv> set \<E>s"

lemma wf_network_system: "network_system \<N>s \<E>s"  by intro_locales

lemma wf_network_system_iff: "p \<in> \<E> \<Longrightarrow> network_system \<N>s \<E>s \<longleftrightarrow> 
(fst p \<in> \<N> \<and> snd p \<in> \<N> \<and> fst p \<noteq> snd p)"
proof -
  assume a1: "p \<in> \<E>"
  then have a2: "snd p \<in> \<N>"
    using network_wf by blast
  have a3: "fst p \<in> \<N>"
    using a1 network_wf by blast
 have "fst p \<noteq> snd p"
    using a1  by (simp add: network_wf)
  then show ?thesis
    using a2 a3 wf_network_system by blast
qed

lemma wf_network1: "\<E> \<subseteq> \<N> \<times> \<N>"
  using network_wf by force

lemma wf_invalid_nodes: "x \<notin> \<N> \<Longrightarrow> p \<in> \<E>  \<Longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p"
  using network_wf by blast

lemma no_self_loop: 
  shows "\<And>e. e \<in> \<E> \<Longrightarrow> fst e \<noteq> snd e"
  using network_wf by simp

lemma exists_nodes : 
  shows "e \<in> \<E> \<Longrightarrow> \<exists> x y. fst e = x \<and> snd e = y \<and> x \<noteq> y"
  using network_wf by auto

end

locale nonempty_network_system = network_system +
assumes edges_nempty: " \<E>s \<noteq> []"
begin


lemma wf_nonempty_netw_list_sys: "nonempty_network_system \<N>s \<E>s"  by intro_locales

lemma wf_nodes_nempty_alt: "\<forall>i \<in> {0..<length \<N>s}.  \<N>s!i \<notin> {}"
  by blast

lemma wf_edges_nempty_alt: "\<forall>j \<in> {0..<length \<E>s}.  \<E>s!i \<notin> {}"
  by blast

lemma nodes_indexing_inj: "\<forall> i \<in> F . i < length \<N>s \<Longrightarrow> inj_on ((!) \<N>s) F"
  by (simp add: distincts inj_on_nth)

lemma edges_indexing_inj: "\<forall> i \<in> F . i < length \<E>s \<Longrightarrow> inj_on ((!) \<E>s) F"
  by (simp add: distincts inj_on_nth)


lemma wf_n_non_zero_imp_m_non_zero: "n > 0 \<Longrightarrow> m > 0"
  using network_wf by fastforce

lemma nodes_product_size: "size (List.product \<N>s \<N>s) = m * m"
  by simp

lemma valid_nodes_index: "i < m \<Longrightarrow> \<N>s ! i \<in> \<N>"
 by auto

lemma valid_nodes_index_cons: "x \<in> \<N> \<Longrightarrow> \<exists> i. \<N>s ! i = x \<and> i < m"
  by (auto simp add: in_set_conv_nth)

lemma valid_nodes_index_obtains: 
  assumes "x \<in> \<N>"
  obtains i where "\<N>s ! i = x \<and> i < m"
  using valid_nodes_index_cons assms by auto

lemma valid_edges_index: "j < n \<Longrightarrow> \<E>s ! j \<in> \<E> "
  by simp

lemma valid_edges_index_cons: "p \<in> \<E>  \<Longrightarrow> \<exists> j . \<E>s ! j = p \<and> j < n"
  by (auto simp add: in_set_conv_nth)

lemma valid_edges_index_obtains: 
  assumes "p \<in> \<E> "
  obtains j where  "\<E>s ! j = p \<and> j < n"
  using assms valid_edges_index_cons by blast

lemma edges_valid_bodies_index: 
  assumes "p \<in> \<E>" "x = fst p"
  obtains i where "i < length \<N>s \<and> \<N>s ! i = x"
  using  valid_edges_index_obtains assms
  by (metis valid_nodes_index_obtains wf_invalid_nodes)

lemma edges_valid_nodes_index: 
  assumes "p \<in> \<E>" "x = fst p" "y = snd p"
  obtains i j where "i < length \<N>s \<and> j < length \<N>s \<and> i \<noteq> j \<and> \<N>s ! i = x \<and> \<N>s ! j = y"
  using  valid_edges_index_obtains assms distincts
  by (metis in_set_conv_nth network_wf)

lemma nodes_list_index_img: "\<N> = image(\<lambda> i . (\<N>s ! i)) ({..<m})"
  using valid_nodes_index_cons valid_nodes_index by auto

lemma edges_list_index_img: "\<E> = image(\<lambda> i . (\<E>s ! i)) ({..<n})"
  using valid_edges_index_cons valid_edges_index by blast


definition I\<^sub>P :: "('a \<times> 'a \<times> 'a) set" where 
"I\<^sub>P \<equiv> {(v,e). e \<in> set \<E>s \<and> fst e = v} " (*edge is directed away from node-positive*)

definition I\<^sub>N :: "('a \<times> 'a \<times> 'a) set" where 
"I\<^sub>N \<equiv> {(v,e). e \<in> set \<E>s \<and> snd e = v} " (*edge is directed toward node-negative*)


definition  "pos_incident  v e \<equiv> (v,e) \<in> I\<^sub>P"
definition  "neg_incident  v e \<equiv> (v,e) \<in> I\<^sub>N"

lemma pos_incident_netw_altdef: 
  assumes "e \<in> set \<E>s"
  shows "pos_incident x e \<longleftrightarrow> fst e = x \<and> fst e \<noteq> snd e"
  using pos_incident_def I\<^sub>P_def assms no_self_loop by auto

lemma  neg_incident_netw_altdef: 
  assumes "e \<in> set \<E>s"
  shows "neg_incident x e \<longleftrightarrow> snd e = x \<and> fst e \<noteq> snd e"
  using neg_incident_def I\<^sub>N_def assms no_self_loop by auto

lemma not_pos_not_neg_incident_netw: 
  assumes "e \<in> set \<E>s"
  shows "\<not> pos_incident x e \<and> \<not> neg_incident x e \<longleftrightarrow> snd e \<noteq> x \<and> fst e \<noteq> x"
  using neg_incident_netw_altdef pos_incident_netw_altdef  assms no_self_loop  by auto

lemma neg_incident_cond_indexed[simp]: "i < m \<Longrightarrow> j < n \<Longrightarrow> neg_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) =  snd (\<E>s ! j)  "
  using neg_incident_netw_altdef valid_nodes_index valid_edges_index  network_wf by auto

lemma pos_incident_cond_indexed[simp]: "i < m \<Longrightarrow> j < n \<Longrightarrow>  pos_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) = fst (\<E>s ! j)"
  using pos_incident_netw_altdef valid_nodes_index valid_edges_index network_wf by auto

lemma pos_not_neg_incident: "i < m \<Longrightarrow> j < n \<Longrightarrow> pos_incident (\<N>s ! i) (\<E>s ! j) \<Longrightarrow> \<not> neg_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) = fst (\<E>s ! j)"
  by (metis neg_incident_netw_altdef no_self_loop nth_mem pos_incident_netw_altdef)

lemma neg_not_pos_incident: "i < m \<Longrightarrow> j < n \<Longrightarrow> neg_incident (\<N>s ! i) (\<E>s ! j) \<Longrightarrow> \<not> pos_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) = snd (\<E>s ! j)"
  by (metis neg_incident_netw_altdef no_self_loop nth_mem pos_incident_netw_altdef)

lemma not_pos_not_neg_incident: "i < m \<Longrightarrow> j < n \<Longrightarrow> \<not> pos_incident (\<N>s ! i) (\<E>s ! j) \<and> \<not> neg_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) \<noteq> snd (\<E>s ! j) \<and> (\<N>s ! i) \<noteq> fst (\<E>s ! j)"
  by auto

lemma bij_betw_nodes_index: "bij_betw (\<lambda> i. \<N>s ! i) {0..<m} \<N>"
proof(simp add: bij_betw_def, intro conjI)
  show "inj_on ((!) \<N>s) {0..<m}"
    by (simp add: nodes_indexing_inj)
  show "(!) \<N>s ` {0..<m} = \<N> "
  proof(intro subset_antisym subsetI)
    fix x assume " x \<in> (!) \<N>s ` {0..<m}"
    then obtain i where "x = \<N>s ! i" and "i<m" by auto
    then show "x \<in> \<N>"
      by(simp add: valid_nodes_index)
  next
    fix x assume "x \<in> \<N>"
    then obtain i where "\<N>s ! i = x" and "i<m" 
      using valid_nodes_index_cons by auto
    then show "x \<in> (!) \<N>s ` {0..<m}" by auto
  qed
qed

lemma bij_betw_edges_index: "bij_betw (\<lambda> i. \<E>s ! i) {0..<n} \<E>"
proof(simp add: bij_betw_def, intro conjI)
  show "inj_on ((!) \<E>s) {0..<n}"
    by(simp add:  edges_indexing_inj)
  show " (!) \<E>s ` {0..<n} = \<E>"
    using edges_list_index_img by force
qed


subsection \<open>Some Basic Network operations\<close>

text \<open>Add a node to a network\<close>
definition  add_node :: "'a node \<Rightarrow> 'a nodes" where
  "add_node v \<equiv> (if v \<in> set \<N>s then \<N>s else (List.insert v \<N>s))"

text \<open>Delete a node to a network\<close>
definition  del_node :: "'a node \<Rightarrow> 'a nodes" where
  "del_node v \<equiv> (if v \<in> set \<N>s then remove1 v \<N>s else \<N>s)"

text \<open>Add an edge to a network\<close>
definition  add_edge :: "'a edge \<Rightarrow> 'a edges" where
  "add_edge e \<equiv> (if e \<in> set \<E>s then \<E>s else (List.insert e \<E>s)) "

text \<open>Delete an edge form a network\<close>
definition del_edge :: "'a edge \<Rightarrow> 'a edges" where
  "del_edge e \<equiv> [p \<leftarrow> (remove1 e \<E>s). p \<noteq> e]" 

text \<open>Delete an edge to a network\<close>
definition del_edge1 :: "'a edge \<Rightarrow> 'a edges" where
  "del_edge1 e \<equiv> [p \<leftarrow> \<E>s. p \<noteq> e]" 

text \<open>Delete an edge to a network\<close>
definition delete_edge :: "'a edge \<Rightarrow> 'a edges" where 
  "delete_edge e =  remove1 e \<E>s"

fun del_edges:: "'a edges \<Rightarrow> 'a edges \<Rightarrow> 'a edges" where
  "del_edges es ps = (if es = ps then [] else [x \<leftarrow> es. x \<notin> set ps])" 

lemma 
  assumes "distinct [a,b,c,d,e]"  "distinct [(a,b),(c,a),(a,b)]" "distinct [(c,d),(e,a),(c,a)]"
  shows "del_edges [(a,b),(c,a),(a,b)] [(c,d),(e,a),(c,a)] = [(c,d),(e,a)]"
  using del_edges.simps assms
  by auto




end
end