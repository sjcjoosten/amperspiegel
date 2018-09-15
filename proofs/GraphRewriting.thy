theory GraphRewriting
imports
  MissingCategory
  LabeledGraphs
  VariableUnification
begin

(* Labeled Graphs form a category *)
type_synonym ('l, 'v) graph_homomorphism
  = "(('l,'v) labeled_graph, 'v rel) Arrow"

locale labeled_graph_category =
  fixes graphtype :: "('l, 'v) labeled_graph \<Rightarrow> bool"
begin

  abbreviation "Graph_Cat \<equiv> Category is_graph_homomorphism graphtype (\<lambda> _ _ _ x y. x O y) (Id_on o vertices)"
  sublocale arrow_category_with_dual Graph_Cat
    by(standard,auto dest:Id_on_vertices_is_identity)

  lemma restrict_iso: (* TODO: move, or clean up 'restrict' altogether *)
        assumes "graphtype X" "graphtype (restrict X)"
        shows "c.iso (arr X (restrict X) (Id_on (vertices X)))"
  by standard (insert assms,cases X,auto)+

end

(* We can think of f and g in a rewrite setting as follows:
   let f be a graph-rewrite-rule, that rewrites L to R: L —f\<longrightarrow> R
   let G be a graph in which L occurs.
   How L occurs in G is described by g, where g be a morphism from L to G.
   The result of the application is the graph G'.
   Here R occurs in G' in the 'same way' as L did in G.
   The notion of 'same way' is formalized via a pushout.
   We cannot guarantee that "graphtype G'", but if it is,
     it is uniquely determined by the pushout, up to isomorphism.

   Although graph rewriting is defined in a rather homogeneous setting,
   we define a pushout in a more heterogeneous setting.
   This helps us get more precise types, so that we know what we're doing.
   When used, 'V = 'R = 'G = 'v
 *)

locale defs_graph_pushout =
 fixes unif :: "('G \<times> 'R) set \<Rightarrow> 'G set \<Rightarrow> 'R set \<Rightarrow> ('G \<times> 'v) set \<times> ('R \<times> 'v) set"
   and f :: "('L \<times> 'R) set" and g :: "('L \<times> 'G) set"
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
  = valid_unification unif + defs_graph_pushout unif f g R G + gc:labeled_graph_category graphtype
  for unif :: "'v rel \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v rel \<times> 'v rel"
  and f g :: "('v \<times> 'v) set"
  and L R G :: "('l,'v) labeled_graph"
  and graphtype :: "('l, 'v) labeled_graph \<Rightarrow> bool" +
  assumes gt [intro]:"graphtype L" "graphtype R" "graphtype G" "graphtype G'"
      and hm [intro]: "is_graph_homomorphism L R f" "is_graph_homomorphism L G g"
begin
  lemma hm_uni:"univalent f" "univalent g" and
        hm_dom:"vertices L = Domain f" "vertices L = Domain g" and
        hm_img:"f `` vertices L \<subseteq> vertices R" "g `` vertices L \<subseteq> vertices G" and
        hm_edg:"edge_preserving f (edges L) (edges R)" "edge_preserving g (edges L) (edges G)"
    using hm unfolding is_graph_homomorphism_def by blast+
  sublocale eq_domain using hm_dom by unfold_locales auto
  
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

  lemma two_routes:
    shows "f O R_to_G' = g O G_to_G'"
    unfolding set_eq_iff relcomp_unfold
  proof(standard,standard,goal_cases)
    case (2 x) then obtain y where y:"(fst x, y) \<in> g \<and> (y, snd x) \<in> G_to_G'" by auto
    then have "fst x \<in> Domain f" using hm(1,2)[unfolded is_graph_homomorphism_def] by auto
    then obtain z where zf:"(fst x,z) \<in> f" by auto
    with y have zs: "(y,z) \<in> eqs" unfolding eq_class_from2_def by auto
    from y eqs_two_routes[OF zs]
    have "(z, snd x) \<in> R_to_G'" by auto
    with zf show ?case by auto
  next
    case (1 x) then obtain y where y:"(fst x, y) \<in> f \<and> (y, snd x) \<in> R_to_G'" by auto
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

  sublocale arrow_pushout gc.Graph_Cat R G L G' f g R_to_G' G_to_G'
  proof(unfold_locales,unfold Category.sel,goal_cases)
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
    finally have eqsa_k: "eqsa O k' \<subseteq> k'" by auto
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
      also note this finally show ?thesis.
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
     
    show ?case proof(standard)
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
    qed next
    show "f O R_to_G' = g O G_to_G'" using two_routes.
  qed auto
end

definition constant_exists where
    "constant_exists K G \<equiv>
       \<forall> k\<in>K. (\<exists> v \<in> vertices G. (k,v,v) \<in> edges G)"
(* Slightly more generic than in the paper: a conflict is any label from a set, rather than a single label *)
definition conflict_free where (* E is the set of conflict edges *)
    "conflict_free E G \<equiv> \<forall> k\<in>E. \<forall> v1 v2. v1 \<in> vertices G \<longrightarrow> v2 \<in> vertices G \<longrightarrow> (k,v1,v2) \<notin> edges G"

lemma preserving_constant_respecting:
  assumes "is_graph_homomorphism G\<^sub>1 G\<^sub>2 f"
          "constant_exists K G\<^sub>1"
  shows "constant_exists K G\<^sub>2"
  unfolding constant_exists_def
proof(standard,goal_cases)
  case (1 k)
  with assms[unfolded constant_exists_def]
  obtain v where v:"v\<in>vertices G\<^sub>1" "(k, v, v) \<in> edges G\<^sub>1" by auto
  with assms[unfolded is_graph_homomorphism_def edge_preserving_def]
  obtain u where u:"(k,u,u) \<in> edges G\<^sub>2" "(v,u) \<in> f" by auto
  with assms[unfolded is_graph_homomorphism_def]
  have "u \<in> vertices G\<^sub>2" by auto
  with u show ?case by auto
qed

lemma copreserving_conflict_free:
  assumes "is_graph_homomorphism G\<^sub>1 G\<^sub>2 f"
          "conflict_free K G\<^sub>2"
  shows "conflict_free K G\<^sub>1"
unfolding conflict_free_def proof(standard+,goal_cases)
  case (1 k v1 v2)
  then obtain u1 u2 where u:"(v1,u1) \<in> f" "(v2,u2) \<in> f"
    using assms[unfolded is_graph_homomorphism_def] by auto
  with assms[unfolded is_graph_homomorphism_def edge_preserving_def] 1
    have "u1 \<in> vertices G\<^sub>2" "u2 \<in> vertices G\<^sub>2" "(k,u1,u2) \<in> edges G\<^sub>2" by auto
  with assms(2)[unfolded conflict_free_def,rule_format,OF 1(1)] show ?case by auto
qed



end