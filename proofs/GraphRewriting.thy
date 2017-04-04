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

lemma relcomp_on_triple[simp]:
  shows "on_triple (R O S) = on_triple R O on_triple S"
 unfolding on_triple_def by fast

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

  lemma variable_distinctness [intro] :
    "variable_distinctness (eq_class_from2 f g) G_only_vertices R_only_vertices"
  proof(standard)
    show "eq_class_from2 f g O (eq_class_from2 f g)\<inverse> O eq_class_from2 f g = eq_class_from2 f g"
      by (fact eq_class_from2_trans_ish)
  qed (auto simp:eq_class_from2_def)

  sublocale variable_distinctness "eq_class_from2 f g" G_only_vertices R_only_vertices
    by standard

  definition "unifs \<equiv> unif (eq_class_from2 f g) G_only_vertices R_only_vertices"
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
  lemma hm_uni:"univalent f" "univalent g" and
        hm_dom:"vertices L = Domain f" "vertices L = Domain g" and
        hm_img:"f `` vertices L \<subseteq> vertices R" "g `` vertices L \<subseteq> vertices G" and
        hm_edg:"edge_preserving f (edges L) (edges R)" "edge_preserving g (edges L) (edges G)"
    using hm unfolding is_graph_homomorphism_def by blast+
  sublocale eq_domain using hm_dom by unfold_locales auto
  abbreviation "comp_rel \<equiv> \<lambda> _ _ _. op O"
  abbreviation "id_vertices \<equiv> Id_on o vertices"
  abbreviation "Graph_Cat \<equiv> (Category is_graph_homomorphism graphtype comp_rel id_vertices)"
  interpretation gc: arrow_category_with_dual Graph_Cat
    by(standard,auto dest:Id_on_vertices_is_identity)
  
  lemma restrict_iso:
        assumes "graphtype X" "graphtype (restrict X)"
        shows "gc.c.iso (gc.arr X (restrict X) (Id_on (vertices X)))"
  by standard (insert assms,cases X,auto)+
  
  sublocale valid_unification_app unif eqs G_only_vertices R_only_vertices G_to_G' R_to_G'
    by(unfold_locales,insert unifs_def,auto)

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
    with y have zs: "(y,z) \<in> eqs" unfolding eq_class_from2_def by auto
    from y eqs_two_routes[OF zs]
    have "(z, snd x) \<in> R_to_G'" by auto
    with zf show ?case by auto
  next
    case (2 x) then obtain y where y:"(fst x, y) \<in> f \<and> (y, snd x) \<in> R_to_G'" by auto
    then have "fst x \<in> Domain g" using hm(1,2)[unfolded is_graph_homomorphism_def] by auto
    then obtain z where zf:"(fst x,z) \<in> g" by auto
    with y have zs: "(z,y) \<in> eqs" unfolding eq_class_from2_def by auto
    from y eqs_two_routes[OF zs]
    have "(z, snd x) \<in> G_to_G'" by auto
    with zf show ?case by auto
  qed
  
  lemma G_to_G'_eqsa:
    "G_to_G' O converse G_to_G' = eqsa \<union> Id_on (vertices G)"
  proof -
    have "G_to_G' O G_to_G'\<inverse> \<subseteq> eqsa \<union> Id_on G_only_vertices" using eqsa by auto
    also have "G_only_vertices \<subseteq> vertices G" by auto
    finally show ?thesis using eqsa by auto
  qed

  lemma R_to_G'_eqsb:
    "R_to_G' O converse R_to_G' = eqsb \<union> Id_on (vertices R)"
  proof -
    have "R_to_G' O R_to_G'\<inverse> \<subseteq> eqsb \<union> Id_on R_only_vertices" using eqsb by auto
    also have "R_only_vertices \<subseteq> vertices R" by auto
    finally show ?thesis using eqsb by auto
  qed

  sublocale arrow_pushout Graph_Cat R G L G' f g R_to_G' G_to_G'
  proof(unfold_locales,goal_cases)
    case (10 D' h' k')
    hence two_ways:"f O h' = g O k'"
      and vo: "graphtype D'"
      and va: "is_graph_homomorphism R D' h'" "is_graph_homomorphism G D' k'" by auto
    let ?a = "converse G_to_G' O k' \<union> converse R_to_G' O h'"
    have vrg:"vertices R = Domain h'" "vertices G = Domain k'"
      and vimg:"h' `` vertices R \<subseteq> vertices D'" "k' `` vertices G \<subseteq> vertices D'"
      and ephk:"edge_preserving h' (edges R) (edges D')" "edge_preserving k' (edges G) (edges D')"
      and vuni:"univalent h'" "univalent k'"
      using va unfolding is_graph_homomorphism_def by blast+
    have vga[intro]: "vertices G' = Domain ?a" unfolding G'_def using vrg by auto
    have vgd_1:"(R_to_G'\<inverse> O h') `` vertices G' \<subseteq> vertices D'" using vimg(1) by auto
    have vgd_2:"(G_to_G'\<inverse> O k') `` vertices G' \<subseteq> vertices D'" using vimg(2) by auto
    have vgd[intro]: "?a `` vertices G' \<subseteq> vertices D'" using vgd_1 vgd_2 unfolding Un_Image by auto
    have eqsb_src: "eqcc f g O f O h' \<subseteq> f O h'" proof fix x
      assume "x \<in> eqcc f g O f O h'"
      then obtain v where v: "(fst x,v) \<in> eqcc f g" "(v,snd x) \<in> f O h'" by (cases x,auto)
      from v(1)[unfolded trancl_power] obtain n where
        "(fst x, v) \<in> (g O g\<inverse> \<union> f O f\<inverse>) ^^ n" by blast
      with v(2) show "x \<in> f O h'" proof(induct n arbitrary:x v)
        case 0 thus ?case by (cases x,auto) next
        case (Suc n)
        then obtain v2 where
          v2:"(fst x, v2) \<in> (g O g\<inverse> \<union> f O f\<inverse>) ^^ n"
             "(v2, v) \<in> (g O g\<inverse> \<union> f O f\<inverse>)" by auto
        then consider "(v2, v) \<in> g O g\<inverse>" | "(v2, v) \<in> f O f\<inverse>" by auto
        hence v2b:"(v2, snd x) \<in> f O h'" proof(cases)
          case 1
          hence "(v2, snd x) \<in> g O (g\<inverse> O g) O k'" using Suc unfolding two_ways by auto
          hence "(v2, snd x) \<in> g O (Id_on (Range g)) O k'" using hm_uni by auto
          then show ?thesis unfolding two_ways by auto
        next
          case 2
          hence "(v2, snd x) \<in> f O (f\<inverse> O f) O h'" using Suc by auto
          hence "(v2, snd x) \<in> f O (Id_on (Range f)) O h'" using hm_uni by auto
          then show ?thesis by auto
        qed
        from Suc(1)[OF v2b v2(1)] show ?case.
      qed
    qed
    hence "eqsb O h' \<subseteq> f\<inverse> O f O h'" unfolding eqsb_is by auto
    also have "f\<inverse> O f O h' = Id_on (Range f) O h'" using hm_uni by auto
    finally have eqsb_h: "eqsb O h' \<subseteq> h'" by auto
    from eqsb_src have "eqcc f g O g O k' \<subseteq> g O k'" unfolding two_ways by auto
    hence "eqsa O k' \<subseteq> g\<inverse> O g O k'" unfolding eqsa_is by auto
    also have "g\<inverse> O g O k' = Id_on (Range g) O k'" using hm_uni by auto
    finally have eqsa_k: "eqsa O k' \<subseteq> k'"  by auto
    have eqs_two_ways: "k'\<inverse> O eqs O h' \<subseteq> Id" proof(standard,goal_cases)
      case (1 x) then obtain v1 v2 where
        v12:"(v1,fst x) \<in> k'" "(v1,v2) \<in> eqs" "(v2,snd x) \<in> h'" by auto
      from exists_org_1[OF v12(2)] obtain a org where
        a: "(org, a) \<in> g" "(org, v2) \<in> f" "(a, v1) \<in> eqsa" by auto
      have "(a,fst x) \<in> k'" using eqsa_k v12(1) a(3) by auto
      hence one:"(org,fst x) \<in> f O h'" unfolding two_ways using a(1) by auto
      have two:"(org, snd x) \<in> f O h'" using a(2) v12(3) by auto
      show ?case using hm_uni vuni one two by (cases x,auto)
    qed
     
    show ?case unfolding Category.sel proof(standard)
      have via_ah:"R_to_G' O ?a = h'" (is ?via_ah)
      proof -
        have "R_to_G' O ?a = R_to_G' O G_to_G'\<inverse> O k' \<union> R_to_G' O R_to_G'\<inverse> O h'" by auto
        also have "R_to_G' O G_to_G'\<inverse> O k' = eqs\<inverse> O k'" using eqs by blast
        also have "R_to_G' O R_to_G'\<inverse> O h' = eqsb O h' \<union> Id_on (vertices R) O h'"
             using R_to_G'_eqsb by blast
        also have "Id_on (vertices R) O h' = h'" using vrg by auto
        also have "eqs\<inverse> O k' = f\<inverse> O (eqcc f g)\<inverse> O g O k'" unfolding eq_class_from2_def by auto
        also have "f\<inverse> O (eqcc f g)\<inverse> O g O k' = eqsb O h'"
             unfolding eqsb_is O_assoc two_ways eqcc_equiv[unfolded sym_conv_converse_eq]..
        also have "eqsb O h' \<union> h' = h'" using eqsb_h by auto
        also finally show ?thesis.
      qed
      have via_ak:"G_to_G' O ?a = k'" (is ?via_ak)
      proof -
        have "G_to_G' O ?a = G_to_G' O R_to_G'\<inverse> O h' \<union> G_to_G' O G_to_G'\<inverse> O k'" by auto
        also have "G_to_G' O R_to_G'\<inverse> O h' = eqs O h'" using eqs by blast
        also have "G_to_G' O G_to_G'\<inverse> O k' = eqsa O k' \<union> Id_on (vertices G) O k'"
             using G_to_G'_eqsa by blast
        also have "Id_on (vertices G) O k' = k'" using vrg by auto
        also have "eqs O h' = g\<inverse> O eqcc f g O f O h'" unfolding eq_class_from2_def by auto
        also have "g\<inverse> O eqcc f g O f O h' = eqsa O k'"
             unfolding eqsa_is O_assoc two_ways eqcc_equiv[unfolded sym_conv_converse_eq]..
        also have "eqsa O k' \<union> k' = k'" using eqsa_k by auto
        also finally show ?thesis.
      qed
      have uni[intro]:"univalent ?a"
        proof(rule univalentI)
        have "k'\<inverse> O (G_to_G' O G_to_G'\<inverse>) O k' \<subseteq> k'\<inverse> O eqsa\<^sup>= O k'" using G_to_G'_eqsa by blast
        also have "eqsa\<^sup>= O k' \<subseteq> k'" using eqsa_k by auto
        also have "k'\<inverse> O k' \<subseteq> Id" using vuni eqsa_k by auto
        finally have a1:"k'\<inverse> O (G_to_G' O G_to_G'\<inverse>) O k' \<subseteq> Id" by auto
        have "h'\<inverse> O (R_to_G' O R_to_G'\<inverse>) O h' \<subseteq> h'\<inverse> O eqsb\<^sup>= O h'" using R_to_G'_eqsb by blast
        also have "eqsb\<^sup>= O h' \<subseteq> h'" using eqsb_h by auto
        also have "h'\<inverse> O h' \<subseteq> Id" using vuni eqsa_k by auto
        finally have a2:"(h'\<inverse> O R_to_G') O R_to_G'\<inverse> O h' \<subseteq> Id" by auto
        have b:"h'\<inverse> O (G_to_G' O R_to_G'\<inverse>)\<inverse> O k' \<subseteq> Id"
               "k'\<inverse> O (G_to_G' O R_to_G'\<inverse>) O h' \<subseteq> Id"
          unfolding eqs using eqs_two_ways by auto
        show "converse ?a O ?a \<subseteq> Id"
          using a1 a2 b unfolding relcomp_distrib2 relcomp_distrib converse_Un converse_relcomp
          converse_converse O_assoc by auto
      qed

      have epa[intro]: "edge_preserving ?a (edges G') (edges D')"
        proof(standard,standard,goal_cases)
          case (1 x)
          obtain l s t where x:"x = (l,s,t)" by(cases x,auto)
          from 1[unfolded G'_def labeled_graph.sel]
          consider "x \<in> (on_triple (G_to_G' O ?a)) `` edges G" |
                   "x \<in> (on_triple (R_to_G' O ?a)) `` edges R" unfolding relcomp_on_triple by auto
          thus "x \<in> edges D'" unfolding via_ak via_ah proof(cases)
            case 1 with edge_preserving_atomic ephk
              show ?thesis unfolding x by (auto simp:on_triple_def) next
            case 2 with edge_preserving_atomic ephk
              show ?thesis unfolding x by (auto simp:on_triple_def)
        qed qed
      have va_a:"is_graph_homomorphism G' D' ?a" (is ?va_a)
        unfolding Category.sel using vga vgd epa by (intro is_graph_homomorphismI,auto)
      show "?va_a \<and> ?via_ah \<and> ?via_ak"
           using va_a via_ah via_ak by auto
      fix u assume "is_graph_homomorphism G' D' u \<and> R_to_G' O u = h' \<and> G_to_G' O u = k'"
      hence va_u:"is_graph_homomorphism G' D' u"
        and via_uh:"R_to_G' O u = h'"
        and via_uk:"G_to_G' O u = k'" by auto
      show "u = ?a" proof
        have "G_to_G'\<inverse> O k' \<subseteq> u" "R_to_G'\<inverse> O h' \<subseteq> u" using via_uk via_uh univalent_RG by auto
        thus subs:"?a \<subseteq> u" by auto
        have d:"Domain ?a = Domain u" using va_a va_u unfolding is_graph_homomorphism_def by auto
        { fix x assume a:"x \<in> u" hence "fst x \<in> Domain ?a" using d by (cases x, auto)
          then obtain v where v:"(fst x,v) \<in> ?a" by auto
          hence "(fst x,v) \<in> u" using subs by auto
          hence "v = snd x" using a va_u unfolding is_graph_homomorphism_def by (cases x, auto)
          hence "x \<in> ?a" using v by auto }
        thus "u \<subseteq> ?a" by auto
      qed
    qed
  qed auto
end

context fixes K::"'l set" begin
  definition constant_respecting where
    "constant_respecting G \<equiv> (\<forall> k\<in>K. \<forall> v1 v2 v3 v4. (k,v1,v2) \<in> edges G \<and> (k,v3,v4) \<in> edges G \<longrightarrow> v1 = v4)"

end

end