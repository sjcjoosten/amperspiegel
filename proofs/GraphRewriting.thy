theory GraphRewriting
imports
  MissingCategory
begin

datatype ('l,'v) labeled_graph = LG (edges:"('l \<times> 'v \<times> 'v) set")

abbreviation entire where
  "entire R \<equiv> Domain R = UNIV"

lemma entire_compose[simp]:
  assumes "entire h1" "entire h2"
  shows "x \<in> Domain (h1 O h2)"
proof -
  obtain y z where "(x,y) \<in> h1" "(y,z) \<in> h2" using assms by blast
  thus ?thesis by auto
qed

type_synonym ('l, 'v) graph_homomorphism
  = "(('l,'v) labeled_graph, 'v rel) Arrow"

definition edge_preserving where
  "edge_preserving h e1 e2 \<equiv> (\<forall> (k,v1,v2) \<in> e1. \<forall> v1' v2'. ((v1, v1') \<in> h \<and> (v2,v2') \<in> h) \<longrightarrow> (k,v1',v2') \<in> e2)"

lemma edge_preserving_atomic:
  assumes "(v1, v1') \<in> h1" "(v2, v2') \<in> h1" "edge_preserving h1 e1 e2" "(k, v1, v2) \<in> e1"
  shows "(k, v1', v2') \<in> e2"
using assms unfolding edge_preserving_def by auto

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

lemma edge_preserving_Id[intro!]:
  "edge_preserving Id x x"
unfolding edge_preserving_def by auto

fun is_graph_homomorphism where
  "is_graph_homomorphism s t h = (entire h \<and> edge_preserving h (edges s) (edges t))"

context fixes K::"'l set" begin
  definition constant_respecting where
    "constant_respecting G \<equiv> \<exists> \<alpha>. inj_on \<alpha> K \<and> (\<forall> k\<in>K. \<forall> v1 v2. (k,v1,v2) \<in> edges G \<longleftrightarrow> (\<alpha> k = v1 \<and> \<alpha> k = v2))"

  interpretation gc:
    ArrowCategory is_graph_homomorphism constant_respecting "\<lambda> _ _ _. op O" "\<lambda> _. Id"
    by(standard,auto)
  find_theorems name:gc
  (* TODO: find a cone in gc.op *)

end