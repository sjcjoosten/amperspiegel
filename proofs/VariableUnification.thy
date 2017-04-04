theory VariableUnification
imports
  Main
begin

definition univalent where "univalent R = (\<forall> x y z. (x,y)\<in> R \<and> (x,z)\<in> R \<longrightarrow> z = y)"

lemma univalent_char : "univalent R \<longleftrightarrow> converse R O R \<subseteq> Id"
  unfolding univalent_def by auto

lemma univalentD [dest]: "univalent R \<Longrightarrow> (x,y)\<in> R \<Longrightarrow> (x,z)\<in> R \<Longrightarrow> z = y"
  unfolding univalent_def by auto

lemma univalentI: "converse R O R \<subseteq> Id \<Longrightarrow> univalent R"
  unfolding univalent_def by auto

lemma univalent_composes[intro]:assumes "univalent R" "univalent S"
 shows "univalent (R O S)" using assms unfolding univalent_char by auto

lemma id_univalent[intro]:"univalent (Id_on x)" unfolding univalent_char by auto

declare sym_Un_converse[intro]


lemma trancl_power_least:
  "p \<in> R\<^sup>+ \<longleftrightarrow> (\<exists>n. p \<in> R ^^ Suc n \<and> (p \<in> R ^^ n \<longrightarrow> n = 0))"
proof
  assume "p \<in> R\<^sup>+"
  from this[unfolded trancl_power] obtain n where p:"n>0" "p \<in> R ^^ n" by auto
  define n' where "n' = n - 1"
  with p have "Suc n' = n" by auto
  with p have "p \<in> R ^^ Suc n'" by auto
  thus "\<exists>n. p \<in> R ^^ Suc n \<and> (p \<in> R ^^ n \<longrightarrow> n = 0)" proof (induct n')
    case 0 hence "p \<in> R ^^ 0 O R \<and> (p \<in> R ^^ 0 \<longrightarrow> 0 = 0)" by auto
    then show ?case by force
  next
    case (Suc n)
    show ?case proof(cases "p \<in> R ^^ Suc n")
      case False with Suc show ?thesis by blast
    qed (rule Suc)
  qed next
  assume "\<exists>n. p \<in> R ^^ Suc n \<and> (p \<in> R ^^ n \<longrightarrow> n = 0)"
  with zero_less_Suc have "\<exists>n>0. p \<in> R ^^ n" by blast
  thus "p \<in> R\<^sup>+" unfolding trancl_power.
qed

lemma refl_on_tranclI :
  assumes "refl_on A r"
  shows "refl_on A (trancl r)"
  proof
    show "r\<^sup>+ \<subseteq> A \<times> A"
      by( rule trancl_subset_Sigma
        , auto simp: assms[THEN refl_onD1] assms[THEN refl_onD2])
    show "\<And>x. x \<in> A \<Longrightarrow> (x, x) \<in> r\<^sup>+"
      using assms[THEN refl_onD] by auto
  qed

definition idempotent where
  "idempotent r \<equiv> r O r = r"

lemma trans_def: "trans r = ((Id \<union> r) O r = r)" "trans r = (r O (Id \<union> r) = r)"
  by(auto simp:trans_def)

lemma idempotent_impl_trans: "idempotent r \<Longrightarrow> trans r"
  by(auto simp:trans_def idempotent_def)

lemma refl_trans_impl_idempotent[intro]: "refl_on A r \<Longrightarrow> trans r \<Longrightarrow> idempotent r"
  by(auto simp:refl_on_def trans_def idempotent_def)

lemma idempotent_subset:
  assumes "idempotent R" "S \<subseteq> R"
  shows "S O R \<subseteq> R" "R O S \<subseteq> R" "S O R O S \<subseteq> R"
  using assms by(auto simp:idempotent_def)

(* equivalence class core *)
abbreviation eqcc where "eqcc f g \<equiv> trancl (g O converse g \<union> f O converse f)"
definition eq_class_from2 where
  "eq_class_from2 f g  \<equiv> converse g O eqcc f g O f"

lemma eqcc_equiv:
  "equiv (Domain g \<union> Domain f) (eqcc f g)"
  "trans (eqcc f g)" "sym (eqcc f g)"
  "idempotent (eqcc f g)" "refl_on (Domain g \<union> Domain f) (eqcc f g)"
proof -
  let ?inner = "g O g\<inverse> \<union> f O f\<inverse>"
  have "sym ?inner" by(rule sym_Un,auto simp:sym_def)
  from sym_trancl[OF this]
  show sym[intro]: "sym (eqcc f g)".
  show trans[intro]: "trans (eqcc f g)" by auto
  have "refl_on (Domain g \<union> Domain f) ?inner" by (rule refl_on_Un,auto simp:refl_on_def)
  thus [intro]:"refl_on (Domain g \<union> Domain f) (eqcc f g)"
     by (auto intro:refl_on_tranclI)
  show "equiv (Domain g \<union> Domain f) (eqcc f g)" by(auto intro:equivI)
  thus "idempotent (eqcc f g)" by auto
qed

lemma equiv_vertices_composites:
  shows "f O f\<inverse> \<subseteq> eqcc f g"
        "g O g\<inverse> \<subseteq> eqcc f g" by auto

lemma range_eqclass:"Range (eq_class_from2 f g) \<subseteq> Range f"
  by (auto simp:eq_class_from2_def)

lemma domain_eqclass:"Domain (eq_class_from2 f g) \<subseteq> Range g"
  by (auto simp:eq_class_from2_def)

lemma eq_class_from2_trans_ish[intro]:
  "eq_class_from2 f g O converse (eq_class_from2 f g) O eq_class_from2 f g = eq_class_from2 f g"
  and eqcc_absorb: "(f O f\<inverse>) O eqcc f g \<subseteq> eqcc f g"
proof
  let ?ev = "trancl (g O converse g \<union> f O converse f)"
  let ?sv = "converse g O ?ev O f"
  from idempotent_subset(1)[OF eqcc_equiv(4) equiv_vertices_composites(1)]
       idempotent_subset(1)[OF eqcc_equiv(4) equiv_vertices_composites(2)]
  have eqs:"(f O f\<inverse>) O eqcc f g \<subseteq> eqcc f g"
           "(g O g\<inverse>) O eqcc f g \<subseteq> eqcc f g".
  from relcomp_mono[OF relcomp_mono[OF subset_refl[of "eqcc f g"] relcomp_mono[OF this]] subset_refl]
  have eq:"\<And> r s. eqcc f g O f O f\<inverse> O eqcc f g O g O g\<inverse> O eqcc f g O s \<subseteq> eqcc f g O s"
   unfolding O_assoc eqcc_equiv[unfolded idempotent_def].
  from relcomp_mono[OF subset_refl this]
  show "eq_class_from2 f g O (eq_class_from2 f g)\<inverse> O eq_class_from2 f g \<subseteq> eq_class_from2 f g"
    unfolding eq_class_from2_def eqcc_equiv[unfolded sym_conv_converse_eq]
              converse_relcomp converse_converse O_assoc.
  show "eq_class_from2 f g \<subseteq> eq_class_from2 f g O (eq_class_from2 f g)\<inverse> O eq_class_from2 f g"
    by (auto simp:eq_class_from2_def)
  from eqs show "(f O f\<inverse>) O eqcc f g \<subseteq> eqcc f g" by blast
qed

lemma eqcc_comm [ac_simps]:
  shows "eqcc f g = eqcc g f" by (auto simp:ac_simps)

declare O_assoc [ac_simps]

lemma domain_enlarge:
  assumes "Range S \<subseteq> Domain R"
  shows "S \<subseteq> S O R O R\<inverse>" proof fix x
  assume "x \<in> S"
  then have v:"(fst x,snd x) \<in> S" by auto
  with assms obtain w where "(snd x,w) \<in> R" by blast
  with v show "x \<in> S O R O R\<inverse>" by (cases x,auto)
qed

locale eq_domain = fixes f g
  assumes dom_eq:"Domain f = Domain g"
  begin
  abbreviation "eqs \<equiv> eq_class_from2 f g"
  abbreviation "eqsa \<equiv> eqs O eqs\<inverse>"
  abbreviation "eqsb \<equiv> eqs\<inverse> O eqs"
  lemma
  shows eqsa_is: "eqsa = g\<inverse> O eqcc f g O g" 
      (is ?eqs_a_is)                                    
    and eqsb_is: "eqsb = f\<inverse> O eqcc f g O f" 
      (is ?eqs_b_is)
    and exists_org:"(a,b) \<in> eqs \<Longrightarrow>
           \<exists>a' b' org. (org,a') \<in> g \<and> (org,b') \<in> f \<and> (a',a) \<in> eqsa  \<and> (b',b) \<in> eqsb"
      (is " _ \<Longrightarrow> ?t3")
    and exists_org_1:"(a,b) \<in> eqs \<Longrightarrow>
           \<exists>a' org. (org,a') \<in> g \<and> (org,b) \<in> f \<and> (a',a) \<in> eqsa"
      (is " _ \<Longrightarrow> ?t1")
    and exists_org_2:"(a,b) \<in> eqs \<Longrightarrow>
           \<exists>b' org. (org,a) \<in> g \<and> (org,b') \<in> f \<and> (b',b) \<in> eqsb"
      (is " _ \<Longrightarrow> ?t2")
  proof -
    note defs = eq_class_from2_def
    from relcomp_mono[OF subset_refl[of "g\<inverse> O eqcc f g"]
                         relcomp_mono[OF eqcc_absorb[of f g] subset_refl[of g]]]
    have eqa:"eqsa \<subseteq> g\<inverse> O eqcc f g O g" 
     unfolding defs eqcc_equiv[unfolded sym_conv_converse_eq] converse_converse
        converse_relcomp using eqcc_equiv(4)[unfolded idempotent_def,of g f]
        using O_assoc by blast
    from relcomp_mono[OF subset_refl[of "f\<inverse> O eqcc f g"]
                         relcomp_mono[OF eqcc_absorb[of g f] subset_refl[of f]]]
    have eqb:"eqsb \<subseteq> f\<inverse> O eqcc f g O f" 
     unfolding defs eqcc_equiv[unfolded idempotent_def sym_conv_converse_eq] converse_converse
        O_assoc converse_relcomp eqcc_comm[of f g]
        using eqcc_equiv(4)[unfolded idempotent_def,of g f] O_assoc by blast
    note a1 = dom_eq
    hence dr:"Range (eqcc f g) \<subseteq> Domain f" by auto
    from relcomp_mono[OF relcomp_mono[OF subset_refl[of "g\<inverse>"] relcomp_mono[OF domain_enlarge[OF this] subset_refl[of "eqcc f g"]]]
                         subset_refl[of g]]
    have "g\<inverse> O eqcc f g O g \<subseteq> eqsa" unfolding defs O_assoc converse_relcomp
         eqcc_equiv[unfolded sym_conv_converse_eq] converse_converse
         using eqcc_equiv(4)[unfolded idempotent_def,of g f] O_assoc by blast
    thus eqs_a_is: ?eqs_a_is using eqa by auto
    from a1 have "Range (eqcc f g) \<subseteq> Domain g" by auto
    from relcomp_mono[OF relcomp_mono[OF subset_refl[of "f\<inverse>"] relcomp_mono[OF domain_enlarge[OF this] subset_refl[of "eqcc f g"]]]
                         subset_refl[of f]]
    have "f\<inverse> O eqcc f g O f \<subseteq> eqsb" unfolding defs O_assoc converse_relcomp
         converse_converse eqcc_equiv[unfolded sym_conv_converse_eq]
        using eqcc_equiv(4)[unfolded idempotent_def,of g f] O_assoc by blast
    thus eqs_b_is: ?eqs_b_is using eqb by auto
    assume a2: "(a,b) \<in> eqs"
    note assms = a1 a2
    from assms[unfolded defs] obtain ov1 ov2 where
         ov12: "(ov1,a) \<in> g" "(ov2,b) \<in> f" "(ov1,ov2) \<in> eqcc f g" by auto
    with a1 obtain b' where b':"(ov1,b') \<in> f" by auto
    hence b_eqs:"(b',b) \<in> eqsb" unfolding eqs_b_is using ov12(2,3) by auto
    have a_eqs:"(a,a) \<in> eqsa" using ov12 unfolding defs by auto
    from ov12(1) b' a_eqs b_eqs show ?t3 ?t2 by auto
    from ov12 a1 obtain a' where a':"(ov2,a') \<in> g" by auto
    from ov12(3) have "(ov1,ov2) \<in> converse (eqcc f g)" 
      unfolding eqcc_equiv[unfolded sym_conv_converse_eq] by auto
    hence a_eqs:"(a',a) \<in> eqsa" unfolding eqs_a_is using a' ov12(1,2) by auto
    have b_eqs:"(b,b) \<in> eqsb" using ov12 unfolding defs by auto
    from ov12(2) a' a_eqs b_eqs show ?t1 by auto
  qed
  
  lemma range_eqs:"Range f = Range eqs"
  proof
    show "Range eqs \<subseteq> Range f" using range_eqclass.
    show "Range f \<subseteq> Range eqs" proof fix x assume "x \<in> Range f" then
      obtain v where f:"(v,x)\<in>f" by auto then
      obtain y where g:"(v,y)\<in>g" using dom_eq by auto
      from f g have "(y,x) \<in> eqs" unfolding eq_class_from2_def by auto
      thus "x \<in> Range eqs" by auto
  qed qed
  
  lemma domain_eqs:"Range g = Domain eqs"
  proof
    show "Domain eqs \<subseteq> Range g" using domain_eqclass.
    show "Range g \<subseteq> Domain eqs" proof fix x assume "x \<in> Range g" then
      obtain v where f:"(v,x)\<in>g" by auto then
      obtain y where g:"(v,y)\<in>f" using dom_eq by auto
      from f g have "(x,y) \<in> eqs" unfolding eq_class_from2_def by auto
      thus "x \<in> Domain eqs" by auto
  qed qed
  
  lemma eqcc_absorb:"f O f\<inverse> O eqcc f g = eqcc f g" (is ?t1)
                    "g O g\<inverse> O eqcc f g = eqcc f g" (is ?t2)
  proof-
    note * = eqcc_equiv[of g f,unfolded refl_on_def] dom_eq Un_absorb
    hence "Range (converse (eqcc f g)) \<subseteq> Domain f"
          "Range (converse (eqcc f g)) \<subseteq> Domain g" by auto
    from this[THEN domain_enlarge(1)]
    have "converse (eqcc f g) \<subseteq> converse (f O f\<inverse> O eqcc f g)"
         "converse (eqcc f g) \<subseteq> converse (g O g\<inverse> O eqcc f g)"
      using *[unfolded sym_converse] by blast+
    with eqcc_absorb[of f g] eqcc_absorb[of g f] eqcc_comm[of f g]
      show ?t1 ?t2 by auto
  qed
end

definition cluster :: "('a \<times> 'b) set \<Rightarrow> (('a \<times> 'b) \<times> ('a \<times> 'b) set) set" where
  "cluster R \<equiv> (\<lambda> p. (p,{(a,b) \<in> R. (a, snd p) \<in> R \<and> (fst p, b) \<in> R})) ` R"

lemma cluster4:
  assumes "x \<in> eqs"
  shows "(x, {(a, b). (a,b) \<in> eqs \<and> (a, snd x) \<in> eqs \<and> (fst x, b) \<in> eqs}) \<in> cluster eqs"
  using assms unfolding cluster_def by auto

locale variable_distinctness =
  fixes eqs :: "('a \<times> 'b) set"
    and lhs :: "'a set"
    and rhs :: "'b set"
  assumes disj:"eqs `` lhs = {}" "converse eqs `` rhs = {}"
      and (* require that eqs is an equivalence relation in a heterogeneous sense *)
          trans_ish[simp]:"eqs O converse eqs O eqs = eqs"
begin
  definition eqs_a :: "'a rel" where
    "eqs_a \<equiv> eqs O converse eqs \<union> Id_on lhs"
  definition eqs_b :: "'b rel" where
    "eqs_b \<equiv> converse eqs O eqs \<union> Id_on rhs"
  lemma refl [intro]:"refl_on (Domain eqs \<union> lhs) eqs_a" "refl_on (Range eqs \<union> rhs) eqs_b"
    using trans unfolding trans_def refl_on_def by (auto simp:eqs_a_def eqs_b_def)
  lemma sym [intro]:"sym eqs_a" "sym eqs_b" by (rule symI, auto simp:eqs_a_def eqs_b_def)+
  lemma trans_part_2[simp]:"converse eqs O eqs O converse eqs = converse eqs" using trans_ish by blast
  lemma trans_part_3[intro]:"(a', b') \<in> eqs \<Longrightarrow> (a, b') \<in> eqs \<Longrightarrow> (a', b) \<in> eqs \<Longrightarrow> (a, b) \<in> eqs" 
    using trans_part_2 trans_ish by blast
  lemma idempotent[intro]:"idempotent eqs_a" "idempotent eqs_b"
    by (auto simp:idempotent_def O_assoc eqs_a_def eqs_b_def)
  lemma trans[intro]:"trans eqs_a" "trans eqs_b" by (intro idempotent[THEN idempotent_impl_trans])+
  lemma eqs_equiv[intro]:
    "equiv (Domain eqs \<union> lhs) eqs_a" "equiv (Range eqs \<union> rhs) eqs_b" by (rule equivI,auto)+
  lemma cluster_dest:
    assumes "((a', b'), S) \<in> cluster eqs"
    shows "(a',b') \<in> eqs" "S = {(a,b). (a, b') \<in> eqs \<and> (a', b) \<in> eqs}"
  proof -
    show el:"(a',b') \<in> eqs" using assms by (auto simp:cluster_def)
    have "S = {(a,b). (a, b) \<in> eqs \<and> (a, b') \<in> eqs \<and> (a', b) \<in> eqs}" using assms cluster4[OF el] by (auto simp:cluster_def)
    thus "S = {(a,b). (a, b') \<in> eqs \<and> (a', b) \<in> eqs}" using trans_part_3[OF el] by auto
  qed
  lemma cluster1:
    assumes "((a,b1),c1) \<in> cluster eqs" "((a,b2),c2) \<in> cluster eqs"
    shows "c1 = c2"
  using cluster_dest[OF assms(2)] cluster_dest[OF assms(1)] by auto
  lemma cluster2:
    assumes "((b1,a),c1) \<in> cluster eqs" "((b2,a),c2) \<in> cluster eqs"
    shows "c1 = c2" 
  using cluster_dest[OF assms(2)] cluster_dest[OF assms(1)] by auto
  lemma cluster3:
    assumes "((aa, ba), bd) \<in> cluster eqs" "((ab, bc), bd) \<in> cluster eqs"
    shows "(aa, bc) \<in> eqs" 
  using cluster_dest[OF assms(2)] cluster_dest[OF assms(1)] by auto
end


locale variable_unification = variable_distinctness +
  fixes nms_a :: "('a \<times> 'c) set"
    and nms_b :: "('b \<times> 'c) set"
  assumes eqs:"nms_a O converse nms_b = eqs" 
      and dom:"Domain eqs \<union> lhs = Domain nms_a"
      and ran:"Range eqs  \<union> rhs = Domain nms_b"
      and inj_lhs:"\<And> a c a'. a \<in> lhs \<Longrightarrow> (a,c) \<in> nms_a \<Longrightarrow> (a',c) \<in> nms_a \<Longrightarrow> a = a'"
      and inj_rhs:"\<And> a c a'. a \<in> rhs \<Longrightarrow> (a,c) \<in> nms_b \<Longrightarrow> (a',c) \<in> nms_b \<Longrightarrow> a = a'"
      and uni_ab':"\<And> a c b c'. (a,c) \<in> nms_a \<Longrightarrow> (b,c') \<in> nms_b \<Longrightarrow> (a,b) \<in> eqs \<Longrightarrow> c = c'"
      and uni_a:"univalent nms_a"
      and uni_b:"univalent nms_b"
begin
  lemma eqs_two_routes:
    assumes "(a,b) \<in> eqs" shows "(a,c) \<in> nms_a \<longleftrightarrow> (b,c) \<in> nms_b"
  proof(rule assms[folded eqs,THEN relcompE],goal_cases)
    case (1 x y z) hence a:"(a, y) \<in> nms_a" "(b, y) \<in> nms_b" by auto
      show ?case proof(standard,goal_cases)
        case 1 show ?case using uni_a 1 a by auto next
        case 2 show ?case using uni_b 2 a by auto
      qed
  qed
  
  lemma eqs_two_routes_inv:
    assumes "(a,c) \<in> nms_a" "(b,c) \<in> nms_b" shows "(a,b) \<in> eqs"
    using assms eqs by auto
  lemma uni_ab:
    "\<And> a c b c'. (a,c) \<in> nms_a \<Longrightarrow> (b,c') \<in> nms_b \<Longrightarrow> (a,b) \<in> eqs \<longleftrightarrow> c = c'"
    using uni_ab' eqs_two_routes_inv eqs by metis
  
  lemma lhs_only:
    assumes "(g', x) \<in> nms_a" "g' \<in> lhs"
    shows "(y,x) \<notin> nms_b"
  proof(rule ccontr)
    assume "\<not> (y, x) \<notin> nms_b" hence "(y, x) \<in> nms_b" by auto
    with eqs assms(1) have "(g',y) \<in> eqs" by auto
    with disj assms(2) show "False" by auto
  qed

  lemma rhs_only:
    assumes "(g', x) \<in> nms_b" "g' \<in> rhs"
    shows "(y,x) \<notin> nms_a"
  proof(rule ccontr)
    assume "\<not> (y, x) \<notin> nms_a" hence "(y, x) \<in> nms_a" by auto
    with eqs assms(1) have "(y,g') \<in> eqs" by auto
    with disj assms(2) show "False" by auto
  qed
  
  lemma eqsa:
    shows "eqs O eqs\<inverse> \<union> Id_on lhs = nms_a O nms_a\<inverse>"
  unfolding set_eq_iff proof(standard,standard,goal_cases)
    case (1 x)
      hence "fst x \<in> Domain nms_a" "snd x \<in> Domain nms_a" using dom[symmetric] by auto
      then obtain v1 v2 where v12: "(fst x,v1) \<in> nms_a" "(snd x,v2) \<in> nms_a" by auto
      from 1 consider "x \<in> eqs O eqs\<inverse>" | "fst x \<in> lhs" "fst x = snd x" by auto
      thus ?case proof(cases)
        case 1 then obtain v where e:"(fst x,v) \<in> eqs" "(snd x,v) \<in> eqs" by auto
        from eqs_two_routes[OF this(1)] v12 have "(v,v1) \<in> nms_b" by auto
        from uni_ab[OF v12(2) this] e have "v1 = v2" by auto
        then show ?thesis using v12 by (cases x, auto) next
        case 2 thus ?thesis using v12 by (cases x,auto)
      qed
    next
    case (2 x)
      then obtain v where v:"(fst x,v) \<in> nms_a" "(snd x,v) \<in> nms_a" by auto
      hence d:"fst x \<in> Domain eqs \<union> lhs" "snd x \<in> Domain eqs \<union> lhs" using dom by auto
      then consider "snd x \<in> lhs" | "snd x \<in> Domain eqs" by auto
      thus ?case proof(cases)
        case 1 from inj_lhs[OF this v(2,1)] this show ?thesis by (cases x,auto) next
        case 2 then obtain v2 where vs:"(snd x,v2) \<in> eqs" by auto
        hence "(v2,v) \<in> nms_b" using eqs_two_routes v by auto
        from eqs_two_routes_inv[OF v(1) this] vs
        show ?thesis by (cases x,auto)
      qed
  qed

  lemma eqsb:
    shows "eqs\<inverse> O eqs \<union> Id_on rhs = nms_b O nms_b\<inverse>"
  unfolding set_eq_iff proof(standard,standard,goal_cases)
    case (1 x)
      hence "fst x \<in> Domain nms_b" "snd x \<in> Domain nms_b" using ran[symmetric] by auto
      then obtain v1 v2 where v12: "(fst x,v1) \<in> nms_b" "(snd x,v2) \<in> nms_b" by auto
      from 1 consider "x \<in> eqs\<inverse> O eqs" | "fst x \<in> rhs" "fst x = snd x" by auto
      thus ?case proof(cases)
        case 1 then obtain v where e:"(v,fst x) \<in> eqs" "(v,snd x) \<in> eqs" by auto
        from eqs_two_routes[OF this(1)] v12 have "(v,v1) \<in> nms_a" by auto
        from uni_ab[OF this v12(2)] e have "v1 = v2" by auto
        then show ?thesis using v12 by (cases x, auto) next
        case 2 thus ?thesis using v12 by (cases x,auto)
      qed
    next
    case (2 x)
      then obtain v where v:"(fst x,v) \<in> nms_b" "(snd x,v) \<in> nms_b" by auto
      hence d:"fst x \<in> Range eqs \<union> rhs" "snd x \<in> Range eqs \<union> rhs" using ran by auto
      then consider "snd x \<in> rhs" | "snd x \<in> Range eqs" by auto
      thus ?case proof(cases)
        case 1 from inj_rhs[OF this v(2,1)] this show ?thesis by (cases x,auto) next
        case 2 then obtain v2 where vs:"(v2,snd x) \<in> eqs" by auto
        hence "(v2,v) \<in> nms_a" using eqs_two_routes v by auto
        from eqs_two_routes_inv[OF this v(1)] vs
        show ?thesis by (cases x,auto)
      qed
  qed
end

locale valid_unification =
  fixes f
  assumes "\<And> eqs lhs rhs. variable_distinctness eqs lhs rhs \<Longrightarrow>
             (case f eqs lhs rhs of (nms_a,nms_b) \<Rightarrow> variable_unification eqs lhs rhs nms_a nms_b)"

locale valid_unification_app = valid_unification + variable_distinctness +
  fixes nms_a nms_b
  assumes app:"(nms_a,nms_b) = f eqs lhs rhs"
begin
  sublocale variable_unification
    using valid_unification_axioms[ unfolded valid_unification_def, rule_format
                                  , OF variable_distinctness_axioms, folded app ] by auto
  
end

datatype ('a,'b) freenaming = freenaming_L 'a | freenaming_R 'b  | freenaming_P "('a \<times> 'b) set"
definition freename :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> ('a, 'b) freenaming) set \<times> ('b \<times> ('a, 'b) freenaming) set" 
  where "freename eqs lhs rhs = ( (\<lambda> ((a,b),c). (a,freenaming_P c)) ` cluster eqs \<union> (\<lambda> a. (a,freenaming_L a)) ` lhs
                                , (\<lambda> ((a,b),c). (b,freenaming_P c)) ` cluster eqs \<union> (\<lambda> a. (a,freenaming_R a)) ` rhs )"
interpretation freename : valid_unification freename
  proof(standard,goal_cases)
    case (1 eqs lhs rhs)
    interpret variable_distinctness eqs lhs rhs using 1.
    show ?case unfolding freename_def prod.case proof(standard,goal_cases)
      case 1
      show ?case unfolding set_eq_iff proof(standard,standard,goal_cases)
        case (1 x)
        then show ?case by (auto dest:cluster3)
      next
        case (2 x)
        { fix xa z
          assume a:"x = (xa, z)"
          with cluster4[OF 2] have e:"(x, {(a, b). (a, b) \<in> eqs \<and> (a, snd x) \<in> eqs \<and> (fst x, b) \<in> eqs}) \<in> cluster eqs" by auto
          let "?y" = "freenaming_P {(a, b). (a, b) \<in> eqs \<and> (a, snd x) \<in> eqs \<and> (fst x, b) \<in> eqs}"
          have "\<exists>x'\<in>cluster eqs. \<forall>a b x2. x' = ((a, b), x2) \<longrightarrow> xa = a \<and> ?y = freenaming_P x2"
               "\<exists>x'\<in>cluster eqs. \<forall>a b x2. x' = ((a, b), x2) \<longrightarrow> z = b \<and> ?y = freenaming_P x2"
            using e a by (metis (lifting) Pair_inject)+
        } note [intro] = this
        hence i:"x \<in> ((\<lambda>((a, b), c). (a, freenaming_P c)) ` cluster eqs O ((\<lambda>((a, b), c). (b, freenaming_P c)) ` cluster eqs)\<inverse>)"
          by (auto simp:relcomp_unfold image_iff prod.split)
        show ?case by (rule subsetD[OF relcomp_mono i]) auto
      qed
    next
      case (4 a c a')
      then show ?case using disj by (auto elim!:cluster_dest)
    next
      case (5 a c a')
      then show ?case using disj by (auto elim!:cluster_dest)
    next
      case (6 a c b c')
      then show ?case using disj by (auto simp:cluster_def)
    next
      case 7
      then show ?case using disj by (auto elim!:cluster_dest cluster1 simp:univalent_def)
    next
      case 8
      then show ?case using disj by (auto elim!:cluster_dest cluster2 simp:univalent_def)
    next
      { fix a x
        assume "(a, x) \<in> eqs" from cluster4[OF this]
        have " x \<in> Domain ((\<lambda>((a, b), c). (b, freenaming_P c)) ` cluster eqs)"
          by (auto intro!:Domain.intros image_eqI)
      } note [intro] = this
      { fix b x
        assume "(x, b) \<in> eqs" from cluster4[OF this]
        have "x \<in> Domain ((\<lambda>((a, b), c). (a, freenaming_P c)) ` cluster eqs)"
          by (auto intro!:Domain.intros image_eqI)
      } note [intro] = this
      have*: "\<And> a b c d. a = Domain c \<Longrightarrow> b = Domain d \<Longrightarrow> a \<union> b = Domain (c \<union> d)"
             "\<And> a b c d. a = Range  c \<Longrightarrow> b = Range  d \<Longrightarrow> a \<union> b = Range  (c \<union> d)" by auto
      case 2 show ?case by (intro *(1),auto elim!:cluster_dest)
      case 3 show ?case by (intro *(1),auto elim!:cluster_dest)
    qed
  qed

end