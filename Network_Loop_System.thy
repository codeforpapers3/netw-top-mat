theory Network_Loop_System
  imports  Network_Incidence_System
begin 


text \<open>This predicate is similar to the one in the directed graph library, but here  all pair of nodes is distinct\<close>
text\<open> This satisfies that there is no self loop in the network system, but it allows multi-edges\<close>

fun pred_netw_dedge_seq :: "'a node  \<Rightarrow> 'a edges \<Rightarrow> 'a node \<Rightarrow> bool" where
  " pred_netw_dedge_seq v1 [] vx = (v1 = vx)" |
  " pred_netw_dedge_seq v1 (p1 # ps) vx = (v1 = fst p1 \<and> fst p1 \<noteq> snd p1 \<and> pred_netw_dedge_seq (snd p1) ps vx)"

lemma pred_netw_path_altdef:
  assumes "ps \<noteq> []"
  shows "pred_netw_dedge_seq v1 ps vx \<longleftrightarrow> fst (hd ps) = v1 \<and> fst (hd ps) \<noteq> snd (hd ps) \<and> pred_netw_dedge_seq (snd (hd ps)) (tl ps) vx"
  using assms by(cases ps) auto

lemma assumes "ps \<noteq> []"
  shows "pred_netw_dedge_seq v1 ps vx \<Longrightarrow> hd ps = (v1, snd (hd ps))"
  using assms pred_netw_path_altdef by fastforce

definition closed_diedge_seq :: "'a node \<Rightarrow> 'a edges \<Rightarrow> bool" where
"closed_diedge_seq v1 ps \<equiv>  pred_netw_dedge_seq v1 ps v1"

definition open_diedge_seq :: "'a node \<Rightarrow> 'a edges \<Rightarrow> 'a node \<Rightarrow> bool" where
"open_diedge_seq v1 ps vx \<equiv>  pred_netw_dedge_seq v1 ps vx \<and> v1 \<noteq> vx"

text \<open>This definition is taken from the network_flow library (by Peter Lammich et al.\<close>
definition train_nodes :: "'a node \<Rightarrow> 'a edges \<Rightarrow> 'a nodes" 
   where "train_nodes v1 ps = v1 # map snd ps"

lemma node_intrain:
"v1 \<in> set (train_nodes v1 ps)"
  using train_nodes_def 
  by (metis list.set_intros(1))


text \<open>These definitions are taken from the directed graph library (by Noschinski)\<close>
definition symcl :: "'a rel \<Rightarrow> 'a rel" ("(_\<^sup>s)" [1000] 999) where
  "symcl R = R \<union> (\<lambda>(a,b). (b,a)) ` R"

lemma symcl_alt: 
  fixes A :: "'a set"
  shows "R \<subseteq> A \<times> A \<longleftrightarrow> symcl R \<subseteq> A \<times> A"
  using symcl_def
  by (metis Un_subset_iff image_mono swap_product)

lemma symcl_elem: "x \<in> R \<Longrightarrow> x \<in> symcl R"
  using symcl_def by auto

primrec reverse :: "'a edges  \<Rightarrow> 'a edges" where
  "reverse [] = []" |
  "reverse (e # es) = reverse es @ [(snd e, fst e)]"

lemma reverse_append[simp]: "reverse (es @ qs) = reverse qs @ reverse es"
  by (induct es) auto

lemma reverse_reverse_list[simp]:
  "reverse (reverse es) = es"
  by (induct es) auto

lemma reverse_empty[simp]:
  "reverse es = [] \<longleftrightarrow> es = []"
  by (induct es) auto 

lemma reverse_eq: "reverse es = reverse qs \<longleftrightarrow> es = qs"
  by (metis reverse_reverse_list)

(*******************************************************)

definition pair_to_set :: "'a edge \<Rightarrow> 'a set" where
"pair_to_set e = {fst e, snd e}"

definition swapair :: "'a edge \<Rightarrow> 'a edge" where
"swapair e = (snd e, fst e)"

context nonempty_network_system
begin

text \<open>The below concept is a generalized concept 
that is considered both directed and semi-directed version of train (walk), path and loop (circuit)\<close>

text\<open>Edge train (walk) with no self-loop is an edge sequence with all edges appearing in the sequence are distinct \<close>

definition is_netw_gen_train :: "'a node \<Rightarrow> 'a edges \<Rightarrow> 'a node \<Rightarrow> bool" where
"is_netw_gen_train v1 ps vx \<equiv> set (map fst ps) \<subseteq> set \<N>s \<and> set (map snd ps) \<subseteq> set \<N>s \<and> set ps \<subseteq> symcl \<E> \<and> fst (hd ps) = v1 \<and> (snd (last ps)) = vx
                                  \<and> pred_netw_dedge_seq v1 ps vx \<and> distinct ps"

lemma is_netw_trainI: " set (map fst ps) \<subseteq> set \<N>s \<Longrightarrow> set (map snd ps) \<subseteq> set \<N>s \<Longrightarrow> set ps \<subseteq> symcl \<E> \<Longrightarrow> fst (hd ps) = v1 \<Longrightarrow>  (snd (last ps)) = vx \<Longrightarrow> pred_netw_dedge_seq v1 ps vx \<Longrightarrow> distinct ps \<Longrightarrow> is_netw_gen_train v1 ps vx"
  using is_netw_gen_train_def by simp 

lemma is_netw_train_wf: "is_netw_gen_train v1 ps vx \<Longrightarrow> set ps \<subseteq> symcl \<E> \<Longrightarrow> fst (hd ps) = v1 \<Longrightarrow> (snd (last ps)) = vx"
  by (simp add: is_netw_gen_train_def)


definition is_gen_closed_train :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_gen_closed_train v1 ps vx \<equiv> is_netw_gen_train v1 ps vx \<and> (fst (hd ps)) = (snd (last ps))"

definition is_gen_open_train :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_gen_open_train v1 ps vx \<equiv> is_netw_gen_train v1 ps vx \<and> (fst (hd ps)) \<noteq> (snd (last ps))"


text \<open>There are two definitions of a path for a directed graph with directed path or semi-directed path includes the case path is a loop (circuit) .
\<close>
text \<open>The below describes a generalized path that allows directed or semi-directed orientation includes the case a path is a circuit, i.e , this path definition contains both open path and closed path\<close>

definition is_netw_gen_path :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_netw_gen_path v1 ps vx \<equiv> is_netw_gen_train v1 ps vx \<and> distinct (tl (train_nodes v1 ps))"

definition is_gen_closed_path :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_gen_closed_path v1 ps vx \<equiv> is_netw_gen_path v1 ps vx \<and> v1 = last (train_nodes v1 ps)"

definition is_gen_open_path :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_gen_open_path v1 ps vx \<equiv> is_netw_gen_path v1 ps vx \<and> v1 \<noteq> last (train_nodes v1 ps)"

definition "Dpath v1 ps vx \<equiv> [e\<leftarrow>ps. is_gen_open_path v1 ps vx]"

definition open_dpath_length :: "'a \<Rightarrow> ('a \<times> 'a) list  \<Rightarrow> nat"  where
"open_dpath_length v1 ps \<equiv> length (Dpath v1 ps (snd (last ps))) -1"

text \<open>Loop is a closed path that the first element of first Network_pair of the path is equal to second element of the last pair of the path\<close>

definition loop ::  "'a edges \<Rightarrow> bool" where
  "loop ps \<equiv> is_gen_closed_path (fst (hd ps)) ps (fst (hd ps)) \<and> (length ps \<ge> 2)"

lemma loop_altdef:
  assumes "distinct ps" and "length ps \<ge> 2" "fst (hd ps) = v1"
  shows "loop ps \<longleftrightarrow> is_gen_closed_path v1 ps v1"
proof(intro iffI)
  show "loop ps \<Longrightarrow> is_gen_closed_path v1 ps v1"
    using assms is_gen_closed_path_def loop_def by blast
  show "is_gen_closed_path v1 ps v1 \<Longrightarrow> loop ps"
    using assms by (simp add: loop_def wf_network_system)
qed

definition loop_list :: " ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
"loop_list ps = [e \<leftarrow> ps. loop ps]"

lemma loop_list_alt: "(hd ps) \<in> set (loop_list ps) \<Longrightarrow> x = fst (hd ps) \<Longrightarrow> is_gen_closed_path x ps x"
  using loop_list_def loop_def is_gen_closed_path_def by force

end 

locale loop_system = nonempty_network_system +
fixes loops_list :: "'a edges list" ("\<L>s")
assumes wellformed_1: "ls \<in> set \<L>s \<Longrightarrow> set ls \<subseteq> symcl \<E> \<and> loop ls \<and> loop (reverse ls)"
assumes wf_2: "\<forall>ls \<in> set \<L>s. x \<in> set (loop_list ls) \<longrightarrow>  x \<notin> set (reverse (loop_list ls))"
and  distinct: "distinct \<L>s" 

begin

abbreviation "l \<equiv> length \<L>s"
abbreviation "\<L> \<equiv> set \<L>s"

lemma wf_loop_system: "loop_system \<N>s \<E>s \<L>s"  by intro_locales

lemma wf_loop_system_iff: 
  assumes "ls \<in> \<L>" and "set ls \<subseteq> symcl \<E>" 
  shows "loop_system \<N>s \<E>s \<L>s  \<longleftrightarrow> loop (ls) \<and>  loop (reverse ls) \<and> set ls \<subseteq> symcl \<E> \<and> (\<forall>ls \<in> set \<L>s.  x \<in> set (loop_list ls) \<longrightarrow>  x \<notin> set (reverse (loop_list ls)))"
  using wellformed_1 wf_loop_system assms wf_2 by blast

lemma edge_in_loop: 
  assumes "ls \<in> \<L>"
  shows "e \<in> set ls \<Longrightarrow>  e \<in> \<E> \<or> e \<in> (\<lambda>(a, b). (b, a)) `\<E> "
  using assms wellformed_1 
  by (smt (verit, best) Un_iff in_mono symcl_def)

lemma edge_node_in_loop: 
  assumes "ls \<in> \<L>" and "fst e \<noteq> snd e"
  shows " e \<in> set ls \<Longrightarrow> fst e \<in> \<N> \<and> snd e \<in> \<N>"
proof
  assume 1: "e \<in> set ls"
  show "fst e \<in> \<N>"
    using assms edge_in_loop network_wf wellformed_1 
    by (smt (verit, best) 1 case_prod_beta fstI imageE)
next
  assume 1: "e \<in> set ls"
  show "snd e \<in> \<N>"
    using assms 1 symcl_def edge_in_loop wellformed_1 
    by (smt (verit) case_prod_beta imageE network_wf snd_conv)
qed

lemma edge_in_ntw_in_loop: 
  assumes "ls \<in> \<L>"
  shows "e \<in> set ls \<Longrightarrow>  e \<in> symcl \<E> \<Longrightarrow> e \<in> \<N> \<times> \<N>"
  using assms wellformed_1 
  by (metis (full_types) subsetD symcl_alt wf_network1)


lemma no_self_loop_in_symcl: 
  shows "\<And>e. e \<in> symcl \<E>  \<Longrightarrow> fst e \<noteq> snd e"
  using Pair_inject Un_iff case_prod_beta no_self_loop symcl_def by fastforce

lemma wf_node_loop: 
  shows " i < length \<L>s \<Longrightarrow> set (\<L>s!i) \<subset> \<N> \<times> \<N>"
proof
show "i < l \<Longrightarrow> set (\<L>s ! i) \<subseteq> \<N> \<times> \<N>"
  proof-
 assume i: "i < l" 
    have "\<And>x. x \<in>  set (\<L>s ! i) \<Longrightarrow> x \<in> \<N> \<times> \<N>"
      using wf_network1  edge_in_loop i 
      by (metis edge_node_in_loop mem_Times_iff no_self_loop_in_symcl nth_mem subset_code(1) wellformed_1)
    then show ?thesis by auto
  qed
  show " i < l \<Longrightarrow> set (\<L>s ! i) \<noteq> \<N> \<times> \<N> "
  proof-
   assume i: "i < l" 
   have 1: "\<And>x. x \<in> set (\<L>s ! i) \<Longrightarrow> fst x \<noteq> snd x"
     using i no_self_loop no_self_loop_in_symcl edge_in_loop edge_node_in_loop 
     by (metis UnI2 nth_mem sup.orderE wellformed_1)
   show ?thesis 
     by (metis "1" SigmaI edges_nempty fst_eqD last_in_set network_wf snd_conv)
 qed
qed

lemma edge_loop1: 
  shows "es \<in> set \<L>s \<Longrightarrow> es = loop_list es"
  using wf_2
  by (simp add: loop_list_def wellformed_1)

lemma edge_rloop1: 
  shows "es \<in> set \<L>s \<Longrightarrow> reverse es = loop_list (reverse es)"
   by (simp add: loop_list_def wellformed_1)

lemma loop_sys_case1: assumes "es \<in> (set \<L>s)"
  shows "x \<in> set (loop_list (reverse es)) \<Longrightarrow> x \<notin> set (loop_list es)"
  using assms wf_2  by (metis edge_loop1 edge_rloop1)


lemma loop_sys_case2: assumes "es \<in> (set \<L>s)"
  shows "x \<notin> set (loop_list (reverse es)) \<Longrightarrow> x \<notin> set (loop_list es) \<or> x \<in> set (loop_list es)"
        "x \<notin> set (loop_list (es)) \<Longrightarrow> x \<notin> set (loop_list (reverse es)) \<or> x \<in> set (loop_list (reverse es))"
      by auto

lemma loop_list_alt:
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows "x \<in> set es \<and> loop es \<and> fst x \<noteq> snd x \<longleftrightarrow> x \<in> set (loop_list es)"
  using  assms exists_nodes loop_list_def by force

lemma reverseloop_list_alt:
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows "x \<in> set (reverse es) \<and> loop es \<and> fst x \<noteq> snd x \<longleftrightarrow> x \<in> set (reverse (loop_list es))"
  using  assms exists_nodes loop_list_def by (simp add: wellformed_1)


end

locale nonempty_loop_system = loop_system +
  assumes loop_list_nempty: " \<L>s \<noteq> []"

begin 

lemma edge_in_loop_pos_inci_node: 
  assumes  "ls \<in> \<L>" 
  shows "\<exists>e \<in> set ls. \<exists>x \<in> set (train_nodes (fst (hd ls)) ls). fst e = x"
proof-
  have 1 : "set ls \<subseteq> symcl \<E>" using wellformed_1 assms(1) by simp 
  have 2: "set (train_nodes (fst (hd ls)) ls) \<subseteq> \<N> " unfolding train_nodes_def
    using assms 1 is_gen_closed_path_def is_netw_gen_train_def is_netw_gen_path_def wellformed_1 
    by (metis (no_types, opaque_lifting) Nil_is_map_conv insert_absorb last.simps last_in_set list.simps(15) list.size(3) loop_def nat.simps(3) numerals(2) order_antisym_conv train_nodes_def zero_order(1))
  from 1 2 obtain e where "e \<in> set ls" and "e \<in> symcl \<E> " using 1 assms 
  by (metis in_mono list.set_sel(1) list.size(3) loop_def nat.simps(3) numerals(2) wellformed_1 zero_order(2))
  hence 5: "\<exists>e \<in> set ls. \<exists>x\<in>set (train_nodes (fst (hd ls)) ls). fst e = x"
    using 2 edge_in_loop edge_node_in_loop assms 
    by (metis emptyE list.set(1) list.set_sel(1) node_intrain)
  thus ?thesis  using 5 by auto
qed

lemma edge_in_loop_neg_inci_node: 
  assumes  "ls \<in> \<L>" 
  shows "\<exists>e \<in> set ls. \<exists>x \<in> set (train_nodes (fst (hd ls)) ls). snd e = x"
  unfolding train_nodes_def using assms
  by (metis imageI image_set list.set_intros(2) edge_in_loop_pos_inci_node)

lemma edge_in_loop_posorneg_inci_node: 
  assumes  "ls \<in> \<L>"  and "x \<in> set (train_nodes (fst (hd ls)) ls)"
  shows "\<exists>e1 e2. fst e1 = x \<and> snd e2 = x \<and> e1 \<noteq> e2"
  using assms edge_in_loop_neg_inci_node edge_in_loop_pos_inci_node 
     no_self_loop_in_symcl wellformed_1 wf_loop_system by fastforce


lemma wf_loop_nempty_alt: "\<forall>k \<in> {0..<length \<L>s}.  \<L>s!k \<notin> {}"
  by blast

lemma wf_edges_nempty_alt: "\<forall>k \<in> {0..<length \<L>s}. (\<forall>j \<in> {0..<length \<E>s}. \<L>s!k!j \<notin> {})"
  by blast

lemma loop_indexing_inj: "\<forall> k \<in> H . k < length \<L>s \<Longrightarrow> inj_on ((!) \<L>s) H"
  using distinct inj_on_nth by blast

lemma wf_loop_edge : "\<forall>k \<in> {0..<length \<L>s}.  set (\<L>s!k) \<subseteq> symcl \<E>"
  using wellformed_1 by auto

text \<open>Basic properties on loop_system \<close>

lemma loop_list_length: "length \<L>s = l"
  by simp

lemma valid_edges_index_cons: 
  assumes "ls \<in>  \<L>" and "p \<in> \<E>"
  shows "p \<in> set ls \<Longrightarrow> \<exists> k. ls ! k = p \<and> k < length ls"
  by (meson in_set_conv_nth)
   
lemma valid_loops_index: "i < l \<Longrightarrow> \<L>s ! i \<in> \<L>"
  using loop_list_length by (metis nth_mem)

lemma valid_loops_index_cons: "ls \<in> \<L> \<Longrightarrow> \<exists> i . \<L>s ! i = ls \<and> i < l"
  by (auto simp add: set_conv_nth)

lemma valid_loops_index_index: " k < length (\<L>s ! i) \<Longrightarrow>  \<L>s ! i ! k \<in> set (\<L>s ! i)"
  by auto

lemma valid_loops_index_index_cons: "p \<in> set (\<L>s ! i)  \<Longrightarrow> \<exists> k . \<L>s ! i ! k = p \<and> k < length (\<L>s ! i) "
  by (meson in_set_conv_nth)

lemma valid_loops_index_obtains: 
  assumes "ls \<in> \<L>"
  obtains i where  "\<L>s ! i = ls \<and> i < l"
  using assms valid_loops_index_cons by auto

lemma loops_set_image: "\<L> = image ( \<lambda> i.  (\<L>s!i)) ({0..<l})"
  by (metis list.set_map map_nth set_upt)

lemma loops_set_list_image: 
  assumes "i < l" 
  shows "set (\<L>s ! i)  = image ( \<lambda> k.  (\<L>s!i!k)) ({0..<length (\<L>s!i)})"
  using distincts by (metis list.set_map map_nth set_upt)

lemma bij_betw_joints_index: "bij_betw (\<lambda> k. \<L>s ! k) {0..<l} \<L>"
proof (simp add: bij_betw_def, intro conjI)
  show "inj_on ((!) \<L>s) {0..<l}"
    by(simp add: loop_indexing_inj)
  show "(!) \<L>s ` {0..<l} =  \<L>"
    using loops_set_image by presburger
qed

text \<open>The loop-edge relationship with orientation and its properties\<close>    

definition "L\<^sub>p \<equiv> {(x, es). x \<in> set \<E>s \<and> es \<in> set \<L>s \<and>  x \<in> set (loop_list es)}"   (*positively oriented loop*)

definition "L\<^sub>n \<equiv> {(x, es) . x \<in> (set \<E>s) \<and> es \<in> set \<L>s \<and> x \<in> set (loop_list (reverse es)) \<and> x \<notin> set (loop_list es)}" (*negatively oriented loop*)

definition in_neg_loop :: "'a \<times> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool"  where
"in_neg_loop x es \<equiv> (x, es) \<in> L\<^sub>n"

definition in_pos_loop :: "'a \<times> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool" where
"in_pos_loop x es \<equiv> (x, es) \<in> L\<^sub>p"


lemma loop_set:
  assumes  "es \<in> (set \<L>s)"
  shows  "x \<in> set es \<and> loop es \<longleftrightarrow> x \<in> set (loop_list es)"
  using assms wellformed_1 loop_def loop_list_def by auto

lemma loop_rev_set:
  assumes   "es \<in> (set \<L>s)"
  shows  "x \<in> set (reverse es) \<and> loop (reverse es) \<longleftrightarrow> x \<in> set (reverse (loop_list es)) \<and> x \<notin> set (loop_list es)"
  using assms L\<^sub>n_def wellformed_1 loop_def loop_list_def wf_2 
  by (smt (verit, best) edge_loop1)


lemma in_neg_loop: 
  assumes "x \<in> (set \<E>s)"
  assumes "es \<in> \<L>" 
  shows "in_neg_loop x es \<longleftrightarrow> x \<in> set (loop_list (reverse (es))) \<and>  x \<notin> set (loop_list es)"
  using assms 
  by (simp add: L\<^sub>n_def in_neg_loop_def)

lemma neg_loop_altdef: 
  assumes "x \<in> (set \<E>s)"
  assumes "es \<in> \<L>" 
  shows "in_neg_loop x es \<longleftrightarrow> x \<in> set (reverse (loop_list es)) \<and> x \<notin> set (loop_list es)"
  using assms
  by (metis edge_loop1 edge_rloop1 in_neg_loop)
 

lemma in_pos_loop: 
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows "in_pos_loop x es \<longleftrightarrow> x \<in> set (loop_list es) "
  using assms
  by (simp add: L\<^sub>p_def in_pos_loop_def)

lemma pos_loop_altdef: 
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows "in_pos_loop x es \<longleftrightarrow> x \<in> set (loop_list es) \<and> x \<notin> set (reverse (loop_list es))  "
  using assms wf_2 in_pos_loop by blast


lemma not_inpos_inneg_loop: 
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows " \<not> in_neg_loop x es \<and> \<not>in_pos_loop x es \<longleftrightarrow> (x \<notin> set (loop_list es)  \<and>  x \<notin>  set (reverse (loop_list es))) \<or> (x \<in> set (loop_list es)  \<and>  x \<in>  set (reverse (loop_list es)))"
  using assms in_pos_loop neg_loop_altdef wf_2 by blast
 

lemma not_inpos_inneg_loop': 
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows " \<not> in_neg_loop x es \<and> \<not>in_pos_loop x es \<longleftrightarrow> x \<notin> set es \<and>  x \<notin>  set (reverse (es))"
  using assms 
  by (metis edge_loop1 not_inpos_inneg_loop wf_2)

lemma wf_pos_loop: assumes "loop_system \<N>s \<E>s \<L>s" 
  shows "in_pos_loop x es \<longrightarrow> loop es \<and> x \<in> set es"
 
  by (simp add: L\<^sub>p_def in_pos_loop_def loop_list_def) 
 
lemma wf_neg_loop: assumes "loop_system \<N>s \<E>s \<L>s" 
  shows "in_neg_loop x es \<longrightarrow> x \<in> set (reverse es)"  
  using L\<^sub>n_def edge_rloop1 in_neg_loop_def wellformed_1 by auto

lemma wf_notin_loop: assumes "nonempty_loop_system \<N>s \<E>s \<L>s"   assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows "\<not>in_neg_loop x es \<and> \<not>in_pos_loop x es \<longrightarrow>  loop (reverse es) \<and>  loop es \<and> ((x \<notin> set (loop_list (reverse es)) \<and> x \<notin> set (loop_list (es))) \<or> (x \<in> set (reverse es) \<and> x \<in> set es))"  
  using assms in_neg_loop in_pos_loop wellformed_1 by auto

lemma in_loop_not_samepos_directed:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s" and "loop es"
shows "\<not> in_pos_loop x es \<Longrightarrow> x \<notin> set (loop_list es) \<and> ( x \<in> set (loop_list (reverse es)) \<or> x \<notin> set (loop_list (reverse es)) )"
  using in_pos_loop_def L\<^sub>p_def assms by blast
 
lemma in_loop_not_oppositeneg_directed:
  assumes "x \<in> \<E>" and "es \<in> set \<L>s" and "loop es"
  shows "\<not> in_neg_loop x es \<Longrightarrow>  in_pos_loop x es \<Longrightarrow> x \<in> set (loop_list es) \<and> x \<notin> set (reverse es)"
  using in_neg_loop_def L\<^sub>n_def assms edge_loop1 pos_loop_altdef by fastforce

lemma neg_loop_cond_indexed[simp]: "k < l \<Longrightarrow> j < n \<Longrightarrow> (\<E>s ! j) \<notin> set (loop_list (\<L>s ! k)) \<Longrightarrow>  in_neg_loop (\<E>s ! j) (\<L>s ! k) \<longleftrightarrow> (\<E>s ! j) \<in> set (reverse (loop_list (\<L>s ! k)))"
  using neg_loop_altdef valid_edges_index valid_loops_index by blast


lemma pos_loop_cond_indexed[simp]: "k < l \<Longrightarrow> j < n \<Longrightarrow> fst (\<E>s ! j) \<noteq> snd (\<E>s ! j) \<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (loop_list (\<L>s ! k)))  \<Longrightarrow> in_pos_loop (\<E>s ! j) (\<L>s ! k) \<longleftrightarrow> (\<E>s ! j) \<in>  set (\<L>s ! k)"
  using valid_edges_index valid_loops_index edge_loop1 in_pos_loop by presburger

lemma in_loop_not_samepos_directed_cond_indexed: "k < l \<Longrightarrow> j < n  \<Longrightarrow> fst (\<E>s ! j) \<noteq> snd (\<E>s ! j) \<Longrightarrow> in_neg_loop (\<E>s ! j) (\<L>s ! k)  \<Longrightarrow> (\<not> in_pos_loop (\<E>s ! j) (\<L>s ! k)) \<longleftrightarrow> (\<E>s ! j) \<notin> set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (loop_list (\<L>s ! k)))"
  by (metis edge_loop1 neg_loop_altdef nth_mem wf_loop_system wf_pos_loop)

lemma not_in_loop_indexed: "k< l \<Longrightarrow> j < n \<Longrightarrow> \<not> (in_pos_loop (\<E>s ! j) (\<L>s ! k))  \<Longrightarrow> \<not> in_neg_loop (\<E>s ! j) (\<L>s ! k)  \<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k)) \<and> (\<E>s ! j) \<notin> set (\<L>s ! k)"
  by (metis filter_True in_loop_not_samepos_directed loop_list_def neg_loop_altdef nth_mem wellformed_1)

lemma in_loop_not_neg_cond_indexed1: "k < l \<Longrightarrow> j < n \<Longrightarrow>  \<not> in_neg_loop (\<E>s ! j) (\<L>s ! k) \<Longrightarrow> in_pos_loop (\<E>s ! j) (\<L>s ! k) \<Longrightarrow> (\<E>s ! j) \<in>  set (\<L>s ! k) "
  using wf_loop_system wf_pos_loop by blast


end
end
