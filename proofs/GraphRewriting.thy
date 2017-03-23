theory GraphRewriting
imports
  MissingCategory
  VariableUnification
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

lemma edge_preserving_Id[intro]: "edge_preserving (Id_on y) x x"
unfolding edge_preserving_def by auto

definition is_graph_homomorphism where
  "is_graph_homomorphism s t h 
    = ( vertices s = Domain h
      \<and> h `` vertices s \<subseteq> vertices t (* TODO: we may wish to take this condition from a context: sometimes relaxing it to allow node-deletions, and sometimes restricting to functions *)
      \<and> edge_preserving h (edges s) (edges t) (* Same applies here, for doing edge deletions or renaming *)
      )"

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

(* Given a relation on vertices, make one on edges *)
definition on_triple where "on_triple R \<equiv> {((l,s,t),(l',s',t')) . l=l' \<and> (s,s') \<in> R \<and> (t,t') \<in> R}"

(* We can think of f and g in a rewrite setting as follows:
   let f be a graph-rewrite-rule, that rewrites L to R: L —f\<longrightarrow> R
   let G be a graph in which L occurs.
   How L occurs in G is described by g, where g be a morphism from L to G.
   The result of the application is the graph G'.
   Here R occurs in G' in the 'same way' as L did in G.
   The notion of 'same way' is formalized via a pushout.
   We cannot guarantee that "graphtype G'", but if it is,
     it is uniquely determined by the pushout, up to isomorphism.

   Although it is defined in a more homogeneous setting,
   we first create a pushout in a heterogeneous setting.
   This helps us get more precise types, so that we know what we're doing.
   When used, 'V = 'R = 'G = 'v
 *)

locale pre_graph_pushout =
 fixes unif :: "('G \<times> 'R) set \<Rightarrow> 'G set \<Rightarrow> 'R set \<Rightarrow> ('G \<times> 'v) set \<times> ('R \<times> 'v) set"
   and f :: "('L \<times> 'R) set" and g :: "('L \<times> 'G) set"
   and L :: "('l, 'L) labeled_graph"
   and R :: "('l, 'R) labeled_graph"
   and G :: "('l, 'G) labeled_graph"
begin
  (* There are three kind of vertices to be distinguished:
     - Vertices in R, with no counterpart in G, i.e. with no counterpart in L
     - Vertices in G, with no counterpart in R, i.e. with no counterpart in L
     - Vertices in both R and G, i.e. sharing some node in L
  *)
  definition "G_only_vertices \<equiv> {v . \<not> (\<exists> l \<in> vertices L. (l,v) \<in> g)}"
  definition "R_only_vertices \<equiv> {v . \<not> (\<exists> l \<in> vertices L. (l,v) \<in> f)}"
  definition "shared_vertices \<equiv> converse g O f"
  definition "unifs \<equiv> unif shared_vertices G_only_vertices R_only_vertices"
  abbreviation "G_to_G' \<equiv> fst unifs"
  abbreviation "R_to_G' \<equiv> snd unifs"
  definition "G' \<equiv> LG (on_triple G_to_G' `` edges G \<union> on_triple R_to_G' `` edges R)
                      (G_to_G' `` vertices G \<union> R_to_G' `` vertices R)"
end


context fixes graphtype :: "('l, 'v) labeled_graph \<Rightarrow> bool"
begin
  abbreviation "comp_rel \<equiv> \<lambda> _ _ _. op O"
  abbreviation "id_vertices \<equiv> Id_on o vertices"
  abbreviation "Graph_Cat \<equiv> (Category is_graph_homomorphism graphtype comp_rel id_vertices)"
  interpretation gc: arrow_category_with_dual Graph_Cat by(standard,auto)
  
  lemma restrict_iso:
        assumes "graphtype g" "graphtype (restrict g)"
        shows "gc.c.iso (gc.arr g (restrict g) (Id_on (vertices g)))"
  by standard (insert assms,cases g,auto)+
  
end 

context fixes K::"'l set" begin
  definition constant_respecting where
    "constant_respecting G \<equiv> (\<forall> k\<in>K. \<forall> v1 v2 v3 v4. (k,v1,v2) \<in> edges G \<and> (k,v3,v4) \<in> edges G \<longrightarrow> v1 = v4)"

end

end