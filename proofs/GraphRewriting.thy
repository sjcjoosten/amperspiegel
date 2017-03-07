theory GraphRewriting
imports
  MissingCategory
begin

datatype ('l,'v) labeled_graph
  = LG (edges:"('l \<times> 'v \<times> 'v) set") (vertices:"'v set")

fun restrict where
  "restrict (LG e v) = LG {(l,v1,v2) \<in> e. v1 \<in> v \<and> v2 \<in> v } v"

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

lemma edge_preserving_Id[intro!]: "edge_preserving (Id_on y) x x"
unfolding edge_preserving_def by auto

definition is_graph_homomorphism where
  "is_graph_homomorphism s t h 
    = ( vertices s = Domain h
      \<and> h `` vertices s \<subseteq> vertices t
      \<and> edge_preserving h (edges s) (edges t))"

lemma is_graph_homomorphism_composes[intro]:
  assumes "is_graph_homomorphism a b x"
          "is_graph_homomorphism b c y"
  shows "is_graph_homomorphism a c (x O y)"
  using assms unfolding is_graph_homomorphism_def by auto blast+

lemma is_graph_homomorphism_Id[intro]:
  shows "is_graph_homomorphism a a (Id_on (vertices a))"
        "is_graph_homomorphism a (restrict a) (Id_on (vertices a))"
        "is_graph_homomorphism (restrict a) a (Id_on (vertices a))"
  unfolding is_graph_homomorphism_def by (cases a;auto simp:edge_preserving_def)+

lemma Id_on_vertices_is_identity[intro]:
  assumes "is_graph_homomorphism a b f"
          "(aa, ba) \<in> f"
  shows "(aa, ba) \<in> Id_on (vertices a) O f"
        "(aa, ba) \<in> f O Id_on (vertices b)"
  using assms unfolding is_graph_homomorphism_def by auto

context fixes graphtype :: "('l, 'a) labeled_graph \<Rightarrow> bool"
begin
  interpretation gc:
    ArrowCategory is_graph_homomorphism graphtype "\<lambda> _ _ _. op O" "Id_on o vertices"
    by(standard,auto)
  
  lemma assumes "graphtype g" "graphtype (restrict g)"
        shows "gc.c.iso (gc.arr g (restrict g) (Id_on (vertices g)))"
  by standard (insert assms,cases g,auto)+
  
end

context fixes K::"'l set" begin
  definition constant_respecting where
    "constant_respecting G \<equiv> \<exists> \<alpha>. inj_on \<alpha> K
       \<and> (\<forall> k\<in>K. \<alpha> k \<in> vertices G
               \<and> (\<forall> v1 v2. (k,v1,v2) \<in> edges G
                       \<longleftrightarrow> (\<alpha> k = v1 \<and> \<alpha> k = v2)))"

  
  
  
  find_theorems name:"local.gc.c."
  (* TODO: find a cone in gc.op *)

end

end