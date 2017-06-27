theory LabeledGraphs
imports MissingRelation
begin

datatype ('l,'v) labeled_graph
  = LG (edges:"('l \<times> 'v \<times> 'v) set") (vertices:"'v set")

fun restrict where
  "restrict (LG e v) = LG {(l,v1,v2) \<in> e. v1 \<in> v \<and> v2 \<in> v } v"

(* Given a relation on vertices, make one on edges *)
definition on_triple where "on_triple R \<equiv> {((l,s,t),(l',s',t')) . l=l' \<and> (s,s') \<in> R \<and> (t,t') \<in> R}"

lemma on_triple[simp]:
  "((l,v1,v2),(l,v3,v4)) \<in> on_triple R \<longleftrightarrow> (v1,v3)\<in> R \<and> (v2,v4) \<in> R"
unfolding on_triple_def by auto

lemma on_tripleD[dest]:
  assumes "((l1,v1,v2),(l2,v3,v4)) \<in> on_triple R"
  shows "l2 = l1" "(v1,v3)\<in> R" "(v2,v4) \<in> R"
 using assms unfolding on_triple_def by auto

lemma relcomp_on_triple[simp]:
  shows "on_triple (R O S) = on_triple R O on_triple S"
 unfolding on_triple_def by fast

definition edge_preserving where
  "edge_preserving h e1 e2 \<equiv> (\<forall> (k,v1,v2) \<in> e1. \<forall> v1' v2'. ((v1, v1') \<in> h \<and> (v2,v2') \<in> h) \<longrightarrow> (k,v1',v2') \<in> e2)"

lemma edge_preserving_atomic:
  assumes "(v1, v1') \<in> h1" "(v2, v2') \<in> h1" "edge_preserving h1 e1 e2" "(k, v1, v2) \<in> e1"
  shows "(k, v1', v2') \<in> e2"
using assms unfolding edge_preserving_def by auto

lemma edge_preserving[intro]:
  assumes "on_triple R `` E \<subseteq> G"
  shows "edge_preserving R E G"
  unfolding edge_preserving_def proof(clarify,goal_cases)
  case (1 a s t v1' v2')
  thus ?case by (intro assms[THEN subsetD]) (auto simp:on_triple_def)
  qed

lemma compose_preserves_edge_preserving[intro]:
  assumes "edge_preserving h1 e1 e2" "edge_preserving h2 e2 e3"
  shows "edge_preserving (h1 O h2) e1 e3" unfolding edge_preserving_def
proof(standard,standard,standard,standard,standard,standard,goal_cases)
  case (1 _ k _ v1 v2 v1'' v2'')
  hence 1:"(k, v1, v2) \<in> e1" "(v1, v1'') \<in> h1 O h2" "(v2, v2'') \<in> h1 O h2" by auto
  then obtain v1' v2' where
    v:"(v1,v1') \<in> h1" "(v1',v1'') \<in> h2" "(v2,v2') \<in> h1" "(v2',v2'') \<in> h2" by auto
  from edge_preserving_atomic[OF v(1,3) assms(1) 1(1)]
       edge_preserving_atomic[OF v(2,4) assms(2)]
  show ?case by metis
qed

lemma edge_preserving_Id[intro]: "edge_preserving (Id_on y) x x"
unfolding edge_preserving_def by auto

definition is_graph_homomorphism where
  "is_graph_homomorphism s t h 
    = ( vertices s = Domain h
      \<and> h `` vertices s \<subseteq> vertices t
      \<and> univalent h
      \<and> edge_preserving h (edges s) (edges t) (* Same applies here, for doing edge deletions or renaming *)
      )"

lemma is_graph_homomorphismI[intro]:
  assumes "vertices s = Domain h"
          "h `` vertices s \<subseteq> vertices t"
          "univalent h"
          "edge_preserving h (edges s) (edges t)"
  shows "is_graph_homomorphism s t h" using assms unfolding is_graph_homomorphism_def by auto

lemma Domain_O:
  assumes "Range x \<subseteq> Domain y"
  shows "Domain x \<subseteq> Domain (x O y)"
  proof fix xa assume "xa \<in> Domain x"
    then obtain w where xa:"(xa,w) \<in> x" by auto
    with assms obtain v where "(w,v) \<in> y" by auto
    with xa have "(xa,v) \<in> x O y" by auto
    thus "xa \<in> Domain (x O y)" by auto qed

lemma is_graph_homomorphism_composes[intro]:
  assumes "is_graph_homomorphism a b x"
          "is_graph_homomorphism b c y"
  shows "is_graph_homomorphism a c (x O y)" proof(standard,goal_cases)
  case 1
    have "Range x \<subseteq> Domain y" using assms(1,2)[unfolded is_graph_homomorphism_def] by blast
    from this[THEN Domain_O]
    have "vertices a \<subseteq> Domain (x O y)" using assms(1)[unfolded is_graph_homomorphism_def] by auto
    thus ?case using assms[unfolded is_graph_homomorphism_def] by auto
  next
  case 2 from assms show ?case unfolding is_graph_homomorphism_def by auto blast 
  qed (insert assms,auto simp:is_graph_homomorphism_def)

lemma is_graph_homomorphism_Id[intro]:
  shows "is_graph_homomorphism a a (Id_on (vertices a))"
        "is_graph_homomorphism a (restrict a) (Id_on (vertices a))"
        "is_graph_homomorphism (restrict a) a (Id_on (vertices a))"
  by (cases a;auto simp:edge_preserving_def)+

lemma Id_on_vertices_is_identity:
  assumes "is_graph_homomorphism a b f"
          "(aa, ba) \<in> f"
  shows "(aa, ba) \<in> Id_on (vertices a) O f"
        "(aa, ba) \<in> f O Id_on (vertices b)"
  using assms unfolding is_graph_homomorphism_def by auto



end