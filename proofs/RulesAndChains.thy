theory RulesAndChains
imports LabeledGraphs
begin

type_synonym ('l,'v) graph_seq = "(nat \<Rightarrow> ('l, 'v) labeled_graph)"

definition chain :: "('l, 'v) graph_seq \<Rightarrow> bool" where
  "chain S \<equiv> \<forall> i. subgraph (S i) (S (i + 1))"

lemma chain_then_restrict:
  assumes "chain S" shows "S i = restrict (S i)"
  using assms[unfolded chain_def is_graph_homomorphism_def] by auto

lemma chain:
  assumes "chain S"
  shows "j \<ge> i \<Longrightarrow> subgraph (S i) (S j)"
proof(induct "j-i" arbitrary:i j)
  case 0
  then show ?case using chain_then_restrict[OF assms] assms[unfolded chain_def] by auto
next
  case (Suc x)
  hence j:"i + x + 1 = j" by auto
  thus ?case
    using subgraph_trans[OF Suc(1) assms[unfolded chain_def,rule_format,of "i+x"],of i,unfolded j]
    using Suc by auto
qed

lemma chain_def2:
  "chain S = (\<forall> i j. j \<ge> i \<longrightarrow> subgraph (S i) (S j))"
proof
  show "chain S \<Longrightarrow> \<forall>i j. i \<le> j \<longrightarrow> subgraph (S i) (S j)" using chain by auto
  show "\<forall>i j. i \<le> j \<longrightarrow> subgraph (S i) (S j) \<Longrightarrow> chain S" unfolding chain_def by simp
qed

definition chain_sup :: "('l, 'v) graph_seq \<Rightarrow> ('l, 'v) labeled_graph" where
  "chain_sup S \<equiv> LG (\<Union> i. edges (S i)) (\<Union> i. vertices (S i))"

lemma chain_sup_subgraph[intro]:
  assumes "chain S"
  shows "subgraph (S j) (chain_sup S)"
proof -
  have c1: "S j = restrict (S j)" for j
    using assms[unfolded chain_def,rule_format,of j] is_graph_homomorphism_def by auto
  hence c2: "chain_sup S = restrict (chain_sup S)"
    unfolding chain_sup_def by auto
  have c3: "graph_union (S j) (chain_sup S) = chain_sup S"
    unfolding chain_sup_def graph_union_def by auto
  show ?thesis unfolding subgraph_def using c1 c2 c3 by auto
qed

type_synonym ('l,'v) Graph_PreRule = "('l, 'v) labeled_graph \<times> ('l, 'v) labeled_graph"

abbreviation graph_rule :: "('l,'v) Graph_PreRule \<Rightarrow> bool" where
"graph_rule R \<equiv> subgraph (fst R) (snd R) \<and> finite_graph (snd R)"

definition set_of_graph_rules :: "('l,'v) Graph_PreRule set \<Rightarrow> bool" where
"set_of_graph_rules Rs \<equiv> \<forall> R\<in>Rs. graph_rule R"

definition agree_on where
"agree_on G f\<^sub>1 f\<^sub>2 \<equiv> (\<forall> v \<in> vertices G. f\<^sub>1 `` {v} = f\<^sub>2 `` {v})"

definition extensible :: "('l,'x) Graph_PreRule \<Rightarrow> ('l,'v) labeled_graph \<Rightarrow> ('x \<times> 'v) set \<Rightarrow> bool"
  where
"extensible R G f \<equiv> (\<exists> g. is_graph_homomorphism (snd R) G g \<and> agree_on (fst R) f g)"

lemma   extensible_chain_sup[intro]:
assumes "chain S" "extensible R (S j) f"
shows "extensible R (chain_sup S) f"
proof -
  from assms obtain g where g:"is_graph_homomorphism (snd R) (S j) g \<and> agree_on (fst R) f g"
    unfolding extensible_def by auto
  have [simp]:"g O Id_on (vertices (S j)) = g" using g[unfolded is_graph_homomorphism_def] by auto
  from g assms(1)
  have "is_graph_homomorphism (snd R) (S j) g" "subgraph (S j) (chain_sup S)" by auto
  from is_graph_homomorphism_composes[OF this]
  have "is_graph_homomorphism (snd R) (chain_sup S) g" by auto
  thus ?thesis using g unfolding extensible_def by blast
qed

definition maintained :: "('l,'x) Graph_PreRule \<Rightarrow> ('l,'v) labeled_graph \<Rightarrow> bool"
  where "maintained R G \<equiv> \<forall> f. is_graph_homomorphism (fst R) G f \<longrightarrow> extensible R G f"

definition consequence_graph
  where "consequence_graph Rs G \<equiv> set_of_graph_rules Rs \<and> (\<forall> R \<in> Rs. maintained R G)"

lemma consequence_graphI[intro]:
  assumes "\<And> R f. R\<in> Rs \<Longrightarrow> is_graph_homomorphism (fst R) G f \<Longrightarrow> extensible R G f"
          "set_of_graph_rules Rs"
  shows "consequence_graph Rs G"
proof-
  have "\<forall>R\<in>Rs. \<forall>f. is_graph_homomorphism (fst R) G f \<longrightarrow> extensible R G f"
  proof fix R
    assume r:"R \<in> Rs"
    show "\<forall>f. is_graph_homomorphism (fst R) G f \<longrightarrow> extensible R G f"
      using r assms by auto
  qed
  thus ?thesis
    unfolding consequence_graph_def maintained_def using assms by auto
qed

(* The paper states:
   'If furthermore S is a subgraph of G,
    and (S, G) is maintained in each consequence graph maintaining Rs,
    then G is a least consequence graph of S maintaining Rs.'
   Note that the type of 'each consequence graph' isn't given here.
   Taken literally, this should mean 'for every possible type'.
   However, I believe it suffices to use the type of G.
   Thus, the property least_consequence_graph is weakened here.
   
   Another reading is that the vertices are from a fixed type everywhere.
   In that case, the least_consequence_graph definition is exactly as in the paper, given 'v='c.
*)
definition least_consequence_graph
  :: "(('l, 'v) Graph_PreRule) set
     \<Rightarrow> ('l, 'c) labeled_graph \<Rightarrow> ('l, 'c) labeled_graph \<Rightarrow> bool"
  where "least_consequence_graph Rs S G \<equiv> consequence_graph Rs G \<and> subgraph S G \<and> 
            (\<forall> C :: ('l, 'c) labeled_graph. consequence_graph Rs C \<longrightarrow> maintained (S,G) C)"

definition fair_chain where
  "fair_chain Rs S \<equiv> set_of_graph_rules Rs \<and> chain S \<and> 
    (\<forall> R f i. (R \<in> Rs \<and> is_graph_homomorphism (fst R) (S i) f) \<longrightarrow> (\<exists> j. extensible R (S j) f))"

lemma fair_chainD:
  assumes "fair_chain Rs S"
  shows "chain S"
        "R \<in> Rs \<Longrightarrow> is_graph_homomorphism (fst R) (S i) f \<Longrightarrow> \<exists> j. extensible R (S j) f"
        "set_of_graph_rules Rs"
  using assms unfolding fair_chain_def by blast+

lemma find_graph_occurence_vertices:
  assumes "chain S" "finite V" "univalent f" "f `` V \<subseteq> vertices (chain_sup S)"
  shows "\<exists> i. f `` V \<subseteq> vertices (S i)"
  using assms(2,4)
proof(induct V)
  case empty thus ?case by auto
next
  case (insert v V)
  from insert.prems have V:"f `` V \<subseteq> vertices (chain_sup S)"
    and v:"f `` {v} \<subseteq> vertices (chain_sup S)" by auto
  from insert.hyps(3)[OF V] obtain i where i:"f `` V \<subseteq> vertices (S i)" by auto
  have "\<exists> j. f `` {v} \<subseteq> vertices (S j)"
  proof(cases "(f `` {v}) = {}")
    case False
    then obtain v' where f:"(v,v') \<in> f" by auto
    hence "v' \<in> vertices (chain_sup S)" using v by auto
    then show ?thesis using assms(3) f unfolding chain_sup_def by auto
  qed auto
  then obtain j where j:"f `` {v} \<subseteq> vertices (S j)" by blast
  have sg:"subgraph (S i) (S (max i j))" "subgraph (S j) (S (max i j))"
    by(rule chain[OF assms(1)],force)+
  have V:"(f \<inter> V \<times> UNIV) `` V \<subseteq> vertices (S (max i j))"
    using i subgraph_subset[OF sg(1)] by auto
  have v:"f `` {v} \<subseteq> vertices (S (max i j))" using j subgraph_subset[OF sg(2)] by auto
  have "f `` insert v V \<subseteq> vertices (S (max i j))" using v V by auto
  thus ?case by blast
qed

lemma find_graph_occurence_edges:
  assumes "chain S" "finite E" "univalent f"
        "on_triple f `` E \<subseteq> edges (chain_sup S)"
      shows "\<exists> i. on_triple f `` E \<subseteq> edges (S i)"
  using assms(2,4)
proof(induct E)
  case empty thus ?case unfolding is_graph_homomorphism_def by auto
next
  case (insert e E)
  have univ:"univalent (on_triple f)" using assms(3) by auto
  have [simp]:"restrict (S i) = S i" for i
    using chain[OF assms(1),unfolded subgraph_def,of i i] by auto
  from insert.prems have E:"on_triple f `` E \<subseteq> edges (chain_sup S)"
    and e:"on_triple f `` {e} \<subseteq> edges (chain_sup S)" by auto
  with insert.hyps obtain i where i:"on_triple f `` E \<subseteq> edges (S i)" by auto
  have "\<exists> j. on_triple f `` {e} \<subseteq> edges (S j)"
  proof(cases "on_triple f `` {e} = {}")
    case False
    then obtain e' where f:"(e,e') \<in> on_triple f" by auto
    hence "e' \<in> edges (chain_sup S)" using e by auto
    then show ?thesis using univ f unfolding chain_sup_def by auto
  qed auto
  then obtain j where j:"on_triple f `` {e} \<subseteq> edges (S j)" by blast
  have sg:"subgraph (S i) (S (max i j))" "subgraph (S j) (S (max i j))"
    by(rule chain[OF assms(1)],force)+
  have E:"on_triple f `` E \<subseteq> edges (S (max i j))"
    using i subgraph_subset[OF sg(1)] by auto
  have e:"on_triple f `` {e} \<subseteq> edges (S (max i j))" using j subgraph_subset[OF sg(2)] by auto
  have "on_triple f `` insert e E \<subseteq> edges (S (max i j))" using e E by auto
  thus ?case by blast
qed

lemma find_graph_occurence:
  assumes "chain S" "finite E" "finite V" "is_graph_homomorphism (LG E V) (chain_sup S) f"
  shows "\<exists> i. is_graph_homomorphism (LG E V) (S i) f"
proof -
  have [simp]:"restrict (S i) = S i" for i
    using chain[OF assms(1),unfolded subgraph_def,of i i] by auto
  from assms[unfolded is_graph_homomorphism_def edge_preserving_simp labeled_graph.sel]
  have u:"univalent f" 
   and e:"on_triple f `` E \<subseteq> edges (chain_sup S)"
   and v:"f `` V \<subseteq> vertices (chain_sup S)"
    by blast+
  from find_graph_occurence_edges[OF assms(1,2) u e]
  obtain i where i:"on_triple f `` E \<subseteq> edges (S i)" by blast
  from find_graph_occurence_vertices[OF assms(1,3) u v]
  obtain j where j:"f `` V \<subseteq> vertices (S j)" by blast
  have sg:"subgraph (S i) (S (max i j))" "subgraph (S j) (S (max i j))"
    by(rule chain[OF assms(1)],force)+
  have e:"on_triple f `` E \<subseteq> edges (S (max i j))"
   and v:"f `` V \<subseteq> vertices (S (max i j))"
    using i j subgraph_subset(2)[OF sg(1)] subgraph_subset(1)[OF sg(2)] by auto
  have "is_graph_homomorphism (LG E V) (S (max i j)) f"
  proof
    from assms[unfolded is_graph_homomorphism_def edge_preserving_simp labeled_graph.sel] e v
    show "vertices (LG E V) = Domain f"
     and "univalent f"
     and "LG E V = restrict (LG E V)"
     and "f `` vertices (LG E V) \<subseteq> vertices (S (max i j))" 
     and "edge_preserving f (edges (LG E V)) (edges (S (max i j)))"
     and "S (max i j) = restrict (S (max i j))" by auto
  qed
  thus ?thesis by auto
qed

lemma fair_chain_impl_consequence_graph: (* Lemma 3 in paper *)
  assumes "fair_chain Rs S"
  shows "consequence_graph Rs (chain_sup S)"
proof
  fix R f assume a:"R \<in> Rs" "is_graph_homomorphism (fst R) (chain_sup S) f"
  hence "fst R = restrict (fst R)" unfolding is_graph_homomorphism_def by auto
  from a fair_chainD(3)[OF assms]
  have fin_v:"finite (vertices (fst R))" unfolding set_of_graph_rules_def
    by (meson finite_subset subgraph_subset)
  from a fair_chainD(3)[OF assms]
  have fin_e:"finite (edges (fst R))" unfolding set_of_graph_rules_def
    by (meson finite_subset is_graph_homomorphism_def subgraph_def2)
  from find_graph_occurence[OF fair_chainD(1)[OF assms] fin_e fin_v] a(2)
  obtain i where "is_graph_homomorphism (fst R) (S i) f" by auto
  from fair_chainD(2)[OF assms a(1) this] obtain j where "extensible R (S j) f" by blast
  thus "extensible R (chain_sup S) f" using fair_chainD(1)[OF assms] by auto
qed (fact fair_chainD[OF assms])

(* Again: the paper allows for arbitrary types in the quantifier..
          the type used here should suffice (and we cannot quantify over types anyways) *)
definition pushout_step ::
    "('a, 'c) Graph_PreRule \<Rightarrow> ('a, 'b) labeled_graph \<Rightarrow> ('a, 'b) labeled_graph \<Rightarrow> bool" where
"pushout_step R G\<^sub>1 G\<^sub>2 \<equiv> graph_rule R \<and> subgraph G\<^sub>1 G\<^sub>2 \<and> 
  (\<exists> f\<^sub>1 f\<^sub>2. is_graph_homomorphism (fst R) G\<^sub>1 f\<^sub>1 \<and>
           is_graph_homomorphism (snd R) G\<^sub>2 f\<^sub>2 \<and>
           f\<^sub>1 \<subseteq> f\<^sub>2 \<and>
           (\<forall> h\<^sub>1 h\<^sub>2 G::('a, 'b) labeled_graph.
             (is_graph_homomorphism (snd R) G h\<^sub>1 \<and>
              is_graph_homomorphism G\<^sub>1 G h\<^sub>2 \<and>
              f\<^sub>1 O h\<^sub>2 \<subseteq> h\<^sub>1) \<longrightarrow> (\<exists> h. is_graph_homomorphism G\<^sub>2 G h \<and> h\<^sub>2 \<subseteq> h))
  )"

definition Simple_WPC ::
    "(('a, 'b) Graph_PreRule) set \<Rightarrow> (('a, 'd) graph_seq) \<Rightarrow> bool" where
"Simple_WPC Rs S \<equiv> set_of_graph_rules Rs \<and> (\<forall> i. \<exists> R \<in> Rs. pushout_step R (S i) (S (i + 1)))"

(* I split up the hard case into two.
   This makes the easy part of the hard case a bit harder,
   but hopefully the overall becomes easier to deal with. *)
inductive WPC ::
    "(('a, 'b) Graph_PreRule) set \<Rightarrow> (('a, 'd) graph_seq) \<Rightarrow> bool"
  where
    wpc_simpl [simp, intro]: "Simple_WPC Rs S \<Longrightarrow> WPC Rs S"
  | wpc_empty [simp, intro]: "chain S \<Longrightarrow> (\<And> i. S i = chain_sup S) \<Longrightarrow> WPC Rs S"
  | wpc_combo [simp, intro]: "(\<And> i. \<exists> S'. S' 0 = S i \<and> chain_sup S' = S (Suc i) \<and> WPC Rs S') \<Longrightarrow> WPC Rs S"



end