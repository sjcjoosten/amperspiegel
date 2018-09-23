theory LabeledGraphs
imports MissingRelation
begin

datatype ('l,'v) labeled_graph
  = LG (edges:"('l \<times> 'v \<times> 'v) set") (vertices:"'v set")

fun restrict where
  "restrict (LG e v) = LG {(l,v1,v2) \<in> e. v1 \<in> v \<and> v2 \<in> v } v"

abbreviation graph where (* is the thing a graph? *)
  "graph X \<equiv> X = restrict X"

abbreviation finite_graph where
  "finite_graph X \<equiv> graph X \<and> finite (vertices X) \<and> finite (edges X)"

lemma restrict_idemp[simp]:
  "restrict (restrict x) = restrict x"
by(cases x,auto)

lemma vertices_restrict[simp]:
  "vertices (restrict G) = vertices G"
  by(cases G,auto)

lemma restrictI[intro]:
  assumes "edges G \<subseteq> {(l,v1,v2). v1 \<in> vertices G \<and> v2 \<in> vertices G }"
  shows "G = restrict G"
  using assms by(cases G,auto)

lemma restrict_subsD[dest]:
  assumes "edges G \<subseteq> edges (restrict G)"
  shows "G = restrict G"
  using assms by(cases G,auto)

lemma restrictD[dest]:
  assumes "G = restrict G"
  shows "edges G \<subseteq> {(l,v1,v2). v1 \<in> vertices G \<and> v2 \<in> vertices G }"
proof -
  have "edges (restrict G) \<subseteq> {(l,v1,v2). v1 \<in> vertices G \<and> v2 \<in> vertices G }" by (cases G,auto)
  thus ?thesis using assms by auto
qed

(* Given a relation on vertices, make one on edges *)
definition on_triple where "on_triple R \<equiv> {((l,s,t),(l',s',t')) . l=l' \<and> (s,s') \<in> R \<and> (t,t') \<in> R}"

lemma on_triple[simp]:
  "((l1,v1,v2),(l2,v3,v4)) \<in> on_triple R \<longleftrightarrow> (v1,v3)\<in> R \<and> (v2,v4) \<in> R \<and> l1 = l2"
unfolding on_triple_def by auto

lemma on_triple_univ[intro!]:
  "univalent f \<Longrightarrow> univalent (on_triple f)"
  unfolding on_triple_def univalent_def by auto

lemma on_tripleD[dest]:
  assumes "((l1,v1,v2),(l2,v3,v4)) \<in> on_triple R"
  shows "l2 = l1" "(v1,v3)\<in> R" "(v2,v4) \<in> R"
 using assms unfolding on_triple_def by auto

lemma on_triple_ID_is_restrict[simp]:
  shows "on_triple (Id_on (vertices G)) `` edges G = edges (restrict G)"
  unfolding on_triple_def by(cases G,auto)

lemma relcomp_on_triple[simp]:
  shows "on_triple (R O S) = on_triple R O on_triple S"
  unfolding on_triple_def by fast

lemma on_triple_preserves_finite[intro]:
"finite E  \<Longrightarrow> finite (on_triple (BNF_Def.Gr A f) `` E)"
  by (auto simp:on_triple_def BNF_Def.Gr_def)

definition edge_preserving where
  "edge_preserving h e1 e2 \<equiv> (\<forall> (k,v1,v2) \<in> e1. \<forall> v1' v2'. ((v1, v1') \<in> h \<and> (v2,v2') \<in> h) \<longrightarrow> (k,v1',v2') \<in> e2)"

lemma edge_preserving_atomic:
  assumes "edge_preserving h1 e1 e2" "(v1, v1') \<in> h1" "(v2, v2') \<in> h1" "(k, v1, v2) \<in> e1"
  shows "(k, v1', v2') \<in> e2"
using assms unfolding edge_preserving_def by auto

lemma edge_preserving[intro]:
  assumes "on_triple R `` E \<subseteq> G"
  shows "edge_preserving R E G"
  unfolding edge_preserving_def proof(clarify,goal_cases)
  case (1 a s t v1' v2')
  thus ?case by (intro assms[THEN subsetD]) (auto simp:on_triple_def)
  qed

lemma edge_preserving_simp:
  shows "edge_preserving R E G \<longleftrightarrow> on_triple R `` E \<subseteq> G"
proof
  assume "edge_preserving R E G"
  hence "\<And> k v1 v2 v1' v2'. (k, v1, v2)\<in>E \<Longrightarrow>
            (v1, v1') \<in> R \<Longrightarrow> (v2, v2') \<in> R \<Longrightarrow> (k, v1', v2') \<in> G"
    unfolding edge_preserving_def by auto
  then show "on_triple R `` E \<subseteq> G" unfolding Image_def by auto
qed auto

lemma edge_preserving_subset:
  assumes "R\<^sub>1 \<subseteq> R\<^sub>2" "E\<^sub>1 \<subseteq> E\<^sub>2" "edge_preserving R\<^sub>2 E\<^sub>2 G"
  shows "edge_preserving R\<^sub>1 E\<^sub>1 G"
  using assms unfolding edge_preserving_def by blast

lemma compose_preserves_edge_preserving:
  assumes "edge_preserving h1 e1 e2" "edge_preserving h2 e2 e3"
  shows "edge_preserving (h1 O h2) e1 e3" unfolding edge_preserving_def
proof(standard,standard,standard,standard,standard,standard,goal_cases)
  case (1 _ k _ v1 v2 v1'' v2'')
  hence 1:"(k, v1, v2) \<in> e1" "(v1, v1'') \<in> h1 O h2" "(v2, v2'') \<in> h1 O h2" by auto
  then obtain v1' v2' where
    v:"(v1,v1') \<in> h1" "(v1',v1'') \<in> h2" "(v2,v2') \<in> h1" "(v2',v2'') \<in> h2" by auto
  from edge_preserving_atomic[OF assms(1) v(1,3) 1(1)]
       edge_preserving_atomic[OF assms(2) v(2,4)]
  show ?case by metis
qed

lemma edge_preserving_Id[intro]: "edge_preserving (Id_on y) x x"
unfolding edge_preserving_def by auto

(* We require vertices s = Domain h to ensure
   that graph homomorphisms are sufficiently unique:
   allowing verties s \<subseteq> Domain h would allow freedom
   on h without influencing t.
   The partiality follows the definition in the paper, per the remark before Def. 7.
   but it means that we cannot use Isabelle's total functions for the homomorphisms.
   We show that graph homomorphisms and embeddings coincide later. *)
definition is_graph_homomorphism where
  "is_graph_homomorphism s t h 
    = ( vertices s = Domain h
      \<and> s = restrict s \<and> t = restrict t
      \<and> h `` vertices s \<subseteq> vertices t
      \<and> univalent h
      \<and> edge_preserving h (edges s) (edges t)
      )"

lemma is_graph_homomorphismI[intro]:
  assumes "vertices s = Domain h"
          "h `` vertices s \<subseteq> vertices t"
          "univalent h"
          "edge_preserving h (edges s) (edges t)"
          "s = restrict s" "t = restrict t"
  shows "is_graph_homomorphism s t h" using assms unfolding is_graph_homomorphism_def by auto

lemma Domain_O:
  assumes "a \<subseteq> Domain x" "x `` a \<subseteq> Domain y"
  shows "a \<subseteq> Domain (x O y)"
  proof fix xa assume xa:"xa \<in> a" hence "xa \<in> Domain x" using assms by auto
    then obtain w where xaw:"(xa,w) \<in> x" by auto
    with xa have "w \<in> Domain y" using assms by auto
    then obtain v where "(w,v) \<in> y" by auto
    with xaw have "(xa,v) \<in> x O y" by auto
    thus "xa \<in> Domain (x O y)" by auto qed

lemma is_graph_homomorphism_composes[intro]:
  assumes "is_graph_homomorphism a b x"
          "is_graph_homomorphism b c y"
  shows "is_graph_homomorphism a c (x O y)" proof(standard,goal_cases)
  case 1
    have "vertices a \<subseteq> Domain x" "x `` vertices a \<subseteq> Domain y"
      using assms(1,2)[unfolded is_graph_homomorphism_def] by blast+
    from this Domain_O[OF this]
    show ?case using assms[unfolded is_graph_homomorphism_def] by auto
  next
  case 2 from assms show ?case unfolding is_graph_homomorphism_def by auto blast 
  qed (insert assms,auto simp:is_graph_homomorphism_def intro:compose_preserves_edge_preserving)

lemma is_graph_homomorphism_Id[intro]:
  shows "is_graph_homomorphism (restrict a) (restrict a) (Id_on (vertices a))"
  by (cases a;auto simp:edge_preserving_def)

lemma Id_on_vertices_is_identity:
  assumes "is_graph_homomorphism a b f"
          "(aa, ba) \<in> f"
  shows "(aa, ba) \<in> Id_on (vertices a) O f"
        "(aa, ba) \<in> f O Id_on (vertices b)"
  using assms unfolding is_graph_homomorphism_def by auto

abbreviation subgraph :: "('a, 'b) labeled_graph \<Rightarrow> ('a, 'b) labeled_graph \<Rightarrow> bool"
  where "subgraph G\<^sub>1 G\<^sub>2 \<equiv> is_graph_homomorphism G\<^sub>1 G\<^sub>2 (Id_on (vertices G\<^sub>1))"

lemma subgraph_trans:
  assumes "subgraph G\<^sub>1 G\<^sub>2" "subgraph G\<^sub>2 G\<^sub>3"
  shows "subgraph G\<^sub>1 G\<^sub>3"
proof-
  from assms[unfolded is_graph_homomorphism_def]
  have "Id_on (vertices G\<^sub>1) O Id_on (vertices G\<^sub>2) = Id_on (vertices G\<^sub>1)"
    by auto
  with is_graph_homomorphism_composes[OF assms] show ?thesis by auto
qed

(* Introducing the map notation just above Def 7 in the paper *)
definition map_graph :: "('c \<times> 'b) set \<Rightarrow> ('a, 'c) labeled_graph \<Rightarrow> ('a, 'b) labeled_graph" where
  "map_graph f G = LG (on_triple f `` (edges G)) (f `` (vertices G))"

lemma map_graph_selectors[simp]:
  "vertices (map_graph f G) = f `` (vertices G)"
  "edges (map_graph f G) = on_triple f `` (edges G)"
  unfolding map_graph_def by auto

lemma map_graph_returns_restricted:
  assumes "vertices G = Domain f"
  shows "map_graph f G = restrict (map_graph f G)"
  using assms by(cases G,auto simp:map_graph_def)

lemma map_graph_preserves_restricted[intro]:
  assumes "graph G"
  shows "graph (map_graph f G)"
proof(rule restrictI,standard) fix x
  assume "x \<in> edges (map_graph f G)"
  with assms show "x \<in> {(l, v1, v2). v1\<in>vertices (map_graph f G) \<and> v2\<in>vertices (map_graph f G)}"
    by(cases x,auto simp:map_graph_def)
qed

lemma map_graph_edge_preserving[intro]:
  shows "edge_preserving f (edges G) (edges (map_graph f G))"
  unfolding map_graph_def by auto

lemma map_graph_is_homo[intro]:
  assumes "univalent f" "vertices G = Domain f" "G = restrict G"
  shows "is_graph_homomorphism G (map_graph f G) f"
proof
  show "f `` vertices G \<subseteq> vertices (map_graph f G)"
    unfolding map_graph_def by auto
  show "edge_preserving f (edges G) (edges (map_graph f G))" by auto
  show "map_graph f G = restrict (map_graph f G)" using assms by auto
qed fact+

lemma map_graph_is_homo_simp:
  "is_graph_homomorphism G (map_graph f G) f
   \<longleftrightarrow> univalent f \<and> vertices G = Domain f \<and> G = restrict G"
proof
  show "is_graph_homomorphism G (map_graph f G) f \<Longrightarrow>
    univalent f \<and> vertices G = Domain f \<and> G = restrict G"
    unfolding is_graph_homomorphism_def by blast
qed auto

abbreviation on_graph where
"on_graph G f \<equiv> BNF_Def.Gr (vertices G) f"

abbreviation map_graph_fn where
"map_graph_fn G f \<equiv> map_graph (on_graph G f) G"

lemma on_graph_id[simp]:
  shows "on_graph B id = Id_on (vertices B)"
  unfolding BNF_Def.Gr_def by auto

lemma in_on_graph[intro]:
  assumes "x \<in> vertices G" "(a x,y) \<in> b"
  shows "(x, y) \<in> on_graph G a O b"
  using assms unfolding BNF_Def.Gr_def by auto

lemma map_graph_fn_id[simp]:
"map_graph_fn X id = restrict X"
"map_graph (Id_on (vertices X)) X = restrict X"
  unfolding BNF_Def.Gr_def map_graph_def on_triple_def by (cases X,force)+

lemma graph_homo[intro!]:
  assumes "graph G"
  shows "is_graph_homomorphism G (map_graph_fn G f) (on_graph G f)"
  using assms unfolding map_graph_is_homo_simp BNF_Def.Gr_def univalent_def by auto

lemma subgraph_subset:
  assumes "subgraph G\<^sub>1 G\<^sub>2"
  shows "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2" "edges (restrict G\<^sub>1) \<subseteq> edges G\<^sub>2"
proof -
  have vrt:"Id_on (vertices G\<^sub>1) `` vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2"
    and ep:"edge_preserving (Id_on (vertices G\<^sub>1)) (edges G\<^sub>1) (edges G\<^sub>2)"
    using assms unfolding is_graph_homomorphism_def by auto
  hence "edges (restrict G\<^sub>1) \<subseteq> edges G\<^sub>2"
    using assms unfolding edge_preserving_simp by auto
  thus "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2" "edges (restrict G\<^sub>1) \<subseteq> edges G\<^sub>2"
    using vrt by auto
qed

lemma subgraph_def2:
  assumes "G\<^sub>1 = restrict G\<^sub>1" "G\<^sub>2 = restrict G\<^sub>2"
  shows "subgraph G\<^sub>1 G\<^sub>2 \<longleftrightarrow> vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2 \<and> edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
proof
  assume "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2 \<and> edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
  hence v:"vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2" and "edges G\<^sub>1 \<subseteq> edges G\<^sub>2" by auto
  hence ep:"edge_preserving (Id_on (vertices G\<^sub>1)) (edges G\<^sub>1) (edges G\<^sub>2)"
    unfolding edge_preserving_def by auto
  show "subgraph G\<^sub>1 G\<^sub>2"
    using assms(2) v ep is_graph_homomorphism_Id[of "G\<^sub>1",folded assms]
    unfolding is_graph_homomorphism_def by auto
next
  assume sg:"subgraph G\<^sub>1 G\<^sub>2"
  hence vrt:"Id_on (vertices G\<^sub>1) `` vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2"
    and ep:"edge_preserving (Id_on (vertices G\<^sub>1)) (edges G\<^sub>1) (edges G\<^sub>2)"
    unfolding is_graph_homomorphism_def by auto
  hence "edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
    using assms unfolding edge_preserving_simp by auto
  thus "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2 \<and> edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
    using vrt by auto
qed

(* Since the set of labels is an implicit type, the notion of graph_union does not completely correspond to the one in the paper *)
definition graph_union where
"graph_union G\<^sub>1 G\<^sub>2 = LG (edges G\<^sub>1 \<union> edges G\<^sub>2) (vertices G\<^sub>1 \<union> vertices G\<^sub>2)"

lemma graph_union_idemp[simp]:
"graph_union A A = A"
"graph_union A (graph_union A B) = (graph_union A B)"
"graph_union A (graph_union B A) = (graph_union B A)"
unfolding graph_union_def by auto

lemma graph_union_vertices[simp]:
"vertices (graph_union G\<^sub>1 G\<^sub>2) = vertices G\<^sub>1 \<union> vertices G\<^sub>2"
  unfolding graph_union_def by auto
lemma graph_union_edges[simp]:
"edges (graph_union G\<^sub>1 G\<^sub>2) = edges G\<^sub>1 \<union> edges G\<^sub>2"
  unfolding graph_union_def by auto

lemma graph_union_preserves_restrict[intro]:
  assumes "G\<^sub>1 = restrict G\<^sub>1" "G\<^sub>2 = restrict G\<^sub>2"
  shows "graph_union G\<^sub>1 G\<^sub>2 = restrict (graph_union G\<^sub>1 G\<^sub>2)"
proof -
  let ?e = "edges G\<^sub>1 \<union> edges G\<^sub>2"
  let ?v = "vertices G\<^sub>1 \<union> vertices G\<^sub>2"
  let ?r = "{(l, v1, v2). (l, v1, v2) \<in> ?e \<and> v1 \<in> ?v \<and> v2 \<in> ?v}" (* restricted edges *)
  { fix l v1 v2
    assume a:"(l,v1,v2) \<in> ?e"
    have "(l,v1,v2) \<in> ?r" proof(cases "(l,v1,v2) \<in> edges (restrict G\<^sub>1)")
      case True
      hence "(l,v1,v2) \<in> edges G\<^sub>1" "v1 \<in> vertices G\<^sub>1" "v2 \<in> vertices G\<^sub>1" by (cases G\<^sub>1;auto)+
      thus ?thesis by auto
    next
      case False hence "(l,v1,v2) \<in> edges (restrict G\<^sub>2)" using a assms by auto
      hence "(l,v1,v2) \<in> edges G\<^sub>2" "v1 \<in> vertices G\<^sub>2" "v2 \<in> vertices G\<^sub>2" by (cases G\<^sub>2;auto)+
      then show ?thesis by auto
    qed
  }
  hence "?e = ?r" by auto
  thus ?thesis unfolding graph_union_def by auto
qed

lemma subgraph_def: (* shows that subgraph matches the definition in the paper *)
"subgraph G\<^sub>1 G\<^sub>2 = (G\<^sub>1 = restrict G\<^sub>1 \<and> G\<^sub>2 = restrict G\<^sub>2 \<and> graph_union G\<^sub>1 G\<^sub>2 = G\<^sub>2)"
proof
  assume assms:"subgraph G\<^sub>1 G\<^sub>2"
  hence r:"G\<^sub>2 = restrict G\<^sub>2" "G\<^sub>1 = restrict G\<^sub>1"
    unfolding is_graph_homomorphism_def by auto
  from subgraph_subset[OF assms]
  have ss:"vertices (restrict G\<^sub>1) \<subseteq> vertices G\<^sub>2" "edges (restrict G\<^sub>1) \<subseteq> edges G\<^sub>2" by auto
  show "G\<^sub>1 = restrict G\<^sub>1 \<and> G\<^sub>2 = restrict G\<^sub>2 \<and> graph_union G\<^sub>1 G\<^sub>2 = G\<^sub>2"
  proof(cases G\<^sub>2)
    case (LG x1 x2) show ?thesis using ss r
    unfolding graph_union_def LG by auto
  qed next
  assume gu: "G\<^sub>1 = restrict G\<^sub>1 \<and> G\<^sub>2 = restrict G\<^sub>2 \<and> graph_union G\<^sub>1 G\<^sub>2 = G\<^sub>2"
  hence sub:"(edges G\<^sub>1 \<union> edges G\<^sub>2) \<subseteq> edges G\<^sub>2"
    "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2"
    unfolding graph_union_def by (cases G\<^sub>2;auto)+
  have r:"G\<^sub>1 = restrict G\<^sub>1" "G\<^sub>2 = restrict G\<^sub>2" using gu by auto
  show "subgraph G\<^sub>1 G\<^sub>2" unfolding subgraph_def2[OF r] using sub by auto
qed

lemma subgraph_refl[simp]: 
"subgraph G G = (G = restrict G)"
  unfolding subgraph_def graph_union_def by(cases G,auto)

lemma subgraph_restrict[simp]:
  "subgraph G (restrict G) = graph G"
  using subgraph_refl subgraph_def by auto

lemma is_graph_homomorphism_def2: (* Shows a graph homomorphism is an embedding as in the paper *)
  shows "is_graph_homomorphism G\<^sub>1 G\<^sub>2 f =
   (vertices G\<^sub>1 = Domain f \<and> univalent f \<and> G\<^sub>1 = restrict G\<^sub>1 \<and> G\<^sub>2 = restrict G\<^sub>2 \<and> graph_union (map_graph f G\<^sub>1) G\<^sub>2 = G\<^sub>2)"
   (is "?lhs = ?rhs")
proof 
  let ?m = "map_graph f G\<^sub>1"
  assume ?rhs
  hence assms : "vertices G\<^sub>1 = Domain f" "univalent f" "G\<^sub>1 = restrict G\<^sub>1"
    and sg: "subgraph ?m G\<^sub>2"
    and f_id:"f O Id_on (f `` vertices G\<^sub>1) = f" unfolding subgraph_def by auto
  hence "edge_preserving (Id_on (vertices ?m)) (edges ?m) (edges G\<^sub>2)"
    unfolding is_graph_homomorphism_def by auto
  hence "on_triple (f O Id_on (f `` vertices G\<^sub>1)) `` edges G\<^sub>1 \<subseteq> edges G\<^sub>2"  (* rewriting peak *)
    unfolding relcomp_Image edge_preserving_simp map_graph_selectors relcomp_on_triple.
  hence "edge_preserving f (edges G\<^sub>1) (edges G\<^sub>2)"
    unfolding edge_preserving_simp f_id.
  thus ?lhs
    using sg assms unfolding is_graph_homomorphism_def
    by auto next
  assume ih:?lhs
  hence "vertices G\<^sub>1 = Domain f \<and> univalent f \<and> G\<^sub>1 = restrict G\<^sub>1 \<and> subgraph (map_graph f G\<^sub>1) G\<^sub>2"
    unfolding is_graph_homomorphism_def edge_preserving_simp
    by auto
  thus ?rhs unfolding subgraph_def by auto
qed

lemma graph_homo_union_id:
assumes "is_graph_homomorphism (graph_union A B) G f"
shows "graph A \<Longrightarrow> is_graph_homomorphism A G (Id_on (vertices A) O f)"
      "graph B \<Longrightarrow> is_graph_homomorphism B G (Id_on (vertices B) O f)"
  using assms unfolding is_graph_homomorphism_def 
  by (auto intro!:edge_preserving dest:edge_preserving_atomic)

end