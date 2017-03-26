theory GraphRewriting
imports
  MissingCategory
  VariableUnification
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

type_synonym ('l, 'v) graph_homomorphism
  = "(('l,'v) labeled_graph, 'v rel) Arrow"

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

locale defs_graph_pushout =
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
  abbreviation "G_only_vertices \<equiv> {v \<in> vertices G . \<not> (\<exists> l. (l,v) \<in> g)}"
  abbreviation "R_only_vertices \<equiv> {v \<in> vertices R . \<not> (\<exists> l. (l,v) \<in> f)}"
  abbreviation "shared_vertices \<equiv> eq_class_from2 f g"

  lemma variable_distinctness [intro] :
    "variable_distinctness shared_vertices G_only_vertices R_only_vertices"
  proof(standard)
    show "shared_vertices O shared_vertices\<inverse> O shared_vertices = shared_vertices"
      by (fact eq_class_from2_trans_ish)
  qed (auto simp:eq_class_from2_def)

  sublocale variable_distinctness shared_vertices G_only_vertices R_only_vertices
    by standard

  definition "unifs \<equiv> unif shared_vertices G_only_vertices R_only_vertices"
  abbreviation "G_to_G' \<equiv> fst unifs"
  abbreviation "R_to_G' \<equiv> snd unifs"
  definition "G' \<equiv> (LG (on_triple G_to_G' `` edges G \<union> on_triple R_to_G' `` edges R)
                       (G_to_G' `` vertices G \<union> R_to_G' `` vertices R))"

  lemma vertex_G'_intro[intro]:
    assumes "e \<in> G_to_G' `` vertices G \<or> e \<in> R_to_G' `` vertices R"
    shows "e \<in> vertices G'"
  using assms unfolding G'_def by auto
  lemma edge_G'_simp[simp]:
    shows "(l,v1,v2) \<in> edges G' \<longleftrightarrow>
             (\<exists> v1' v2'. (l,v1',v2')   \<in> edges G \<and> (v1',v1)  \<in> G_to_G' \<and> (v2',v2)  \<in> G_to_G')
           \<or> (\<exists> v1'' v2''. (l,v1'',v2'') \<in> edges R \<and> (v1'',v1) \<in> R_to_G' \<and> (v2'',v2) \<in> R_to_G')"
  unfolding G'_def on_triple_def by auto

end

locale pre_graph_pushout
  = valid_unification unif + defs_graph_pushout unif f g L R G 
  for unif :: "'v rel \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v rel \<times> 'v rel"
  and f g
  and L R G :: "('l,'v) labeled_graph" + 
  fixes graphtype :: "('l, 'v) labeled_graph \<Rightarrow> bool"
  assumes gt [intro]:"graphtype L" "graphtype R" "graphtype G" "graphtype G'"
      and hm [intro]: "is_graph_homomorphism L R f" "is_graph_homomorphism L G g"
begin
  abbreviation "comp_rel \<equiv> \<lambda> _ _ _. op O"
  abbreviation "id_vertices \<equiv> Id_on o vertices"
  abbreviation "Graph_Cat \<equiv> (Category is_graph_homomorphism graphtype comp_rel id_vertices)"
  interpretation gc: arrow_category_with_dual Graph_Cat
    by(standard,auto dest:Id_on_vertices_is_identity)

  lemma restrict_iso:
        assumes "graphtype X" "graphtype (restrict X)"
        shows "gc.c.iso (gc.arr X (restrict X) (Id_on (vertices X)))"
  by standard (insert assms,cases X,auto)+
  
  sublocale variable_unification shared_vertices G_only_vertices R_only_vertices G_to_G' R_to_G'
    using valid_unification_axioms[unfolded valid_unification_def,rule_format,OF variable_distinctness]
    unfolding unifs_def by auto

  lemma vertices_Domain [simp]: "vertices R = Domain R_to_G'" "vertices G = Domain G_to_G'"
    proof -
    { fix l x assume *:"(l, x) \<in> f"
      hence **:"l \<in> Domain g" using hm(1,2)[unfolded is_graph_homomorphism_def] by auto
      have "x \<in> Range (g\<inverse> O eqcc f g O f)"
        apply (intro Range.intros relcomp.intros)
        by (insert * **,auto intro:someI)
    } note [dest] = this
    { fix l x assume *:"(l, x) \<in> g"
      hence **:"l \<in> Domain f" using hm(1,2)[unfolded is_graph_homomorphism_def] by auto
      have "x \<in> Domain (g\<inverse> O eqcc f g O f)"
        apply (intro Domain.intros relcomp.intros)
        by (insert * **,auto intro:someI)
    } note [dest] = this
    show "vertices R = Domain R_to_G'" unfolding ran[symmetric]
      using hm(1)[unfolded is_graph_homomorphism_def] by (auto simp:eq_class_from2_def)
    show "vertices G = Domain G_to_G'" unfolding dom[symmetric]
      using hm(2)[unfolded is_graph_homomorphism_def] by (auto simp:eq_class_from2_def)
  qed
  
  lemma univalent_RG[intro]: "univalent R_to_G'" "univalent G_to_G'"
    using uni_a uni_b unfolding univalent_def 
  by (auto simp:eq_class_from2_def)
  
  lemma is_hom[intro]:
    shows "is_graph_homomorphism R G' R_to_G'" "is_graph_homomorphism G G' G_to_G'"
    unfolding is_graph_homomorphism_def by (auto simp:G'_def)
  (* The other direction does not hold: converse R_to_G' is not total or univalent *)

  lemma two_routes[simp]:
    shows "g O G_to_G' = f O R_to_G'"
    unfolding set_eq_iff relcomp_unfold
  proof(standard,standard,goal_cases)
    case (1 x) then obtain y where y:"(fst x, y) \<in> g \<and> (y, snd x) \<in> G_to_G'" by auto
    then have "fst x \<in> Domain f" using hm(1,2)[unfolded is_graph_homomorphism_def] by auto
    then obtain z where zf:"(fst x,z) \<in> f" by auto
    with y have zs: "(y,z) \<in> shared_vertices" unfolding eq_class_from2_def by auto
    from y eqs_two_routes[OF zs]
    have "(z, snd x) \<in> R_to_G'" by auto
    with zf show ?case by auto
  next
    case (2 x) then obtain y where y:"(fst x, y) \<in> f \<and> (y, snd x) \<in> R_to_G'" by auto
    then have "fst x \<in> Domain g" using hm(1,2)[unfolded is_graph_homomorphism_def] by auto
    then obtain z where zf:"(fst x,z) \<in> g" by auto
    with y have zs: "(z,y) \<in> shared_vertices" unfolding eq_class_from2_def by auto
    from y eqs_two_routes[OF zs]
    have "(z, snd x) \<in> G_to_G'" by auto
    with zf show ?case by auto
  qed
  
  sublocale arrow_pushout Graph_Cat R G L G' f g R_to_G' G_to_G'
  proof(unfold_locales,goal_cases)
    case (10 D' h' k')
    hence two_ways:" f O h' = g O k'"
      and vo: "graphtype D'"
      and va: "is_graph_homomorphism R D' h'" "is_graph_homomorphism G D' k'" by auto
    have vrg:"vertices R = Domain h'" "vertices G = Domain k'"
      and vimg:"h' `` vertices R \<subseteq> vertices D'" "k' `` vertices G \<subseteq> vertices D'"
      and ephk:"edge_preserving h' (edges R) (edges D')" "edge_preserving k' (edges G) (edges D')"
      and vuni:"univalent h'" "univalent k'"
      using va unfolding is_graph_homomorphism_def by blast+
    show ?case unfolding Category.sel proof(standard)
      let ?a = "converse G_to_G' O k' \<union> converse R_to_G' O h'"
      have uni[intro]:"univalent ?a" using vuni sorry
      have vga[intro]: "vertices G' = Domain ?a" unfolding G'_def using vrg by auto
      have vgd_1:"(R_to_G'\<inverse> O h') `` vertices G' \<subseteq> vertices D'" using vimg(1) by auto
      have vgd_2:"(G_to_G'\<inverse> O k') `` vertices G' \<subseteq> vertices D'" using vimg(2) by auto
      have vgd[intro]: "?a `` vertices G' \<subseteq> vertices D'" using vgd_1 vgd_2 unfolding Un_Image by auto
      have via_ah:"R_to_G' O ?a = h'" (is ?via_ah)
      proof -
        have "shared_vertices \<inverse> O k' \<subseteq> h'" sorry
        hence c1:"R_to_G' O G_to_G'\<inverse> O k' \<subseteq> h'" unfolding eqs[symmetric] by auto
        have c2:"R_to_G' O R_to_G'\<inverse> O h' \<subseteq> h'" apply auto sorry
        have c3:"h' \<subseteq> R_to_G' O R_to_G'\<inverse> O h'" apply auto sorry
        show ?thesis using c1 c2 c3 by auto
      qed
      have via_ak:"G_to_G' O ?a = k'" (is ?via_ak) sorry
      have epa[intro]: "edge_preserving ?a (edges G') (edges D')"
        proof(standard,standard,goal_cases)
          case (1 x)
          obtain l s t where x:"x = (l,s,t)" by(cases x,auto)
          from 1[unfolded G'_def labeled_graph.sel]
          consider "x \<in> on_triple ?a `` on_triple G_to_G' `` edges G" |
                   "x \<in> on_triple ?a `` on_triple R_to_G' `` edges R" by auto
          thus "x \<in> edges D'" proof(cases)
            case 1 show ?thesis proof (rule 1[THEN ImageE],goal_cases)
              case (1 g_tr)
              then obtain s' t' where g_tr:"g_tr = (l,s',t')" unfolding x by (cases g_tr,auto)
              from 1[unfolded x g_tr] obtain s'' t''
                where G:"(l,s'',t'') \<in> edges G" "(s'',s') \<in> G_to_G'" "(t'',t') \<in> G_to_G'" by auto
              hence "s'' \<in> vertices G" "t'' \<in> vertices G" by auto
              then have st0:"(s'',s) \<in> k'" "(t'',t) \<in> k'" using vrg via_ak G 1 sorry
              from edge_preserving_atomic[OF st0 ephk(2) G(1)]
              show ?case unfolding x.
            qed
          next
            case 2
            then show ?thesis sorry
          qed
        qed
      have va_a:"is_graph_homomorphism G' D' ?a" (is ?va_a)
        unfolding Category.sel using vga vgd epa by (intro is_graph_homomorphismI,auto)
      show "?va_a \<and> ?via_ah \<and> ?via_ak"
           using va_a via_ah via_ak by auto
      fix u assume "is_graph_homomorphism G' D' u \<and> R_to_G' O u = h' \<and> G_to_G' O u = k'"
      hence va_u:"is_graph_homomorphism G' D' u"
        and via_uh:"R_to_G' O u = h'"
        and via_uk:"G_to_G' O u = k'" by auto
      then show "u = ?a" apply auto sorry
    qed
  qed auto
end

context fixes K::"'l set" begin
  definition constant_respecting where
    "constant_respecting G \<equiv> (\<forall> k\<in>K. \<forall> v1 v2 v3 v4. (k,v1,v2) \<in> edges G \<and> (k,v3,v4) \<in> edges G \<longrightarrow> v1 = v4)"

end

end