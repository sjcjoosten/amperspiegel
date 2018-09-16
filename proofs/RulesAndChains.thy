theory RulesAndChains
imports LabeledGraphs
begin

type_synonym ('l,'v) graph_seq = "(nat \<Rightarrow> ('l, 'v) labeled_graph)"

definition chain :: "('l, 'v) graph_seq \<Rightarrow> bool" where
  "chain S \<equiv> \<forall> i. subgraph (S i) (S (i + 1))"

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
"graph_rule R \<equiv> subgraph (fst R) (snd R) \<and> finite (vertices (snd R))"

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

lemma find_graph_occurence:
  assumes "chain S" "finite V"
  shows "is_graph_homomorphism (LG E V) (chain_sup S) f \<Longrightarrow> (\<exists> i. is_graph_homomorphism (LG E V) (S i) f)"
  using assms(2)
proof(induct V arbitrary:E f)
  have chf:"subgraph (S i) (chain_sup S)" for i using assms(1) chain_sup_subgraph by auto
  hence rst:"S i = restrict (S i)" for i unfolding is_graph_homomorphism_def by auto
  case empty
  then show ?case unfolding is_graph_homomorphism_def using rst by auto
next
  case (insert v V E f)
  let ?E = "edges (restrict (LG E V))"
  let ?f = "f Int (V \<times> UNIV)"
  from insert.prems have ep:"edge_preserving f E (edges (chain_sup S))"
    and domF:"insert v V = Domain f"
    and vert:"f `` vertices (LG E (insert v V)) \<subseteq> vertices (chain_sup S)"
    unfolding is_graph_homomorphism_def by auto
  from insert.hyps have "Domain (f \<inter> V \<times> UNIV) = Domain f \<inter> V" by auto
  with domF have dom: "Domain (f \<inter> V \<times> UNIV) = V" by (auto simp:Domain_Int_subset)
  have ep:"edge_preserving ?f ?E (edges (chain_sup S))"
    by (rule edge_preserving_subset[OF _ _ ep],auto)
  have "is_graph_homomorphism (LG ?E V) (chain_sup S) ?f"
    apply(rule is_graph_homomorphismI)
    using insert.prems ep unfolding dom is_graph_homomorphism_def univalent_def by auto
  with insert.hyps obtain i where i:"is_graph_homomorphism (LG ?E V) (S i) ?f" by auto
  obtain v' where f:"(v,v') \<in> f" using domF by auto
  hence "v' \<in> vertices (chain_sup S)" using vert by auto
  then obtain j where j:"v' \<in> vertices (S j)" unfolding chain_sup_def by auto
  have "is_graph_homomorphism (LG E (insert v V)) (S (max i j)) f"
    using i j f sorry
  thus ?case by blast
qed

lemma fair_chain_impl_consequence_graph: (* Lemma 3 in paper *)
  assumes "fair_chain Rs S"
  shows "consequence_graph Rs (chain_sup S)"
proof
  fix R f assume a:"R \<in> Rs" "is_graph_homomorphism (fst R) (chain_sup S) f"
  hence "fst R = restrict (fst R)" unfolding is_graph_homomorphism_def by auto
  from a fair_chainD(3)[OF assms]
  have "finite (vertices (fst R))" unfolding set_of_graph_rules_def
    by (meson finite_subset subgraph_subset)
  from find_graph_occurence[OF fair_chainD(1)[OF assms] this, of "edges (fst R)"] a(2)
  obtain i where "is_graph_homomorphism (fst R) (S i) f" by auto
  from fair_chainD(2)[OF assms a(1) this] obtain j where "extensible R (S j) f" by blast
  thus "extensible R (chain_sup S) f" using fair_chainD(1)[OF assms] by auto
qed (fact fair_chainD[OF assms])


end