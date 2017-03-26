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

locale variable_unification =
  fixes eqs :: "('a \<times> 'b) set"
    and lhs :: "'a set"
    and rhs :: "'b set"
    and nms_a :: "('a \<times> 'c) set"
    and nms_b :: "('b \<times> 'c) set"
  assumes eqs:"nms_a O converse nms_b = eqs"
      and dom:"Domain eqs \<union> lhs = Domain nms_a"
      and ran:"Range eqs  \<union> rhs = Domain nms_b"
      and inj_a:"\<And> a c a'. a \<in> lhs \<Longrightarrow> (a,c) \<in> nms_a \<Longrightarrow> (a',c) \<in> nms_a \<Longrightarrow> a = a'"
      and inj_b:"\<And> a c a'. a \<in> rhs \<Longrightarrow> (a,c) \<in> nms_b \<Longrightarrow> (a',c) \<in> nms_b \<Longrightarrow> a = a'"
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
end

declare sym_Un_converse[intro]

lemma refl_on_trancl :
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
     by (auto intro:refl_on_trancl)
  show "equiv (Domain g \<union> Domain f) (eqcc f g)" by(auto intro:equivI)
  thus "idempotent (eqcc f g)" by auto
qed

lemma equiv_vertices_composites:
  shows "f O f\<inverse> \<subseteq> eqcc f g"
        "g O g\<inverse> \<subseteq> eqcc f g" by auto

lemma range_eqcc:"Range (eq_class_from2 f g) \<subseteq> Range f"
  by (auto simp:eq_class_from2_def)

lemma domain_eqcc:"Domain (eq_class_from2 f g) \<subseteq> Range g"
  by (auto simp:eq_class_from2_def)

lemma eq_class_from2_trans_ish[intro]:
  "eq_class_from2 f g O converse (eq_class_from2 f g) O eq_class_from2 f g = eq_class_from2 f g"
proof
  let ?ev = "trancl (g O converse g \<union> f O converse f)"
  let ?sv = "converse g O ?ev O f"
  from idempotent_subset(1)[OF eqcc_equiv(4) equiv_vertices_composites(1)]
       idempotent_subset(1)[OF eqcc_equiv(4) equiv_vertices_composites(2)]
  have "(f O f\<inverse>) O eqcc f g \<subseteq> eqcc f g"
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
qed


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
  abbreviation eqs_a :: "'a rel" where
    "eqs_a \<equiv> eqs O converse eqs"
  abbreviation eqs_b :: "'b rel" where
    "eqs_b \<equiv> converse eqs O eqs"
  lemma refl [intro]:"refl_on (Domain eqs) eqs_a" "refl_on (Range eqs) eqs_b"
    using trans unfolding trans_def refl_on_def by auto
  lemma sym [intro]:"sym eqs_a" "sym eqs_b" by (rule symI, auto)+
  lemma trans_part_2[simp]:"converse eqs O eqs O converse eqs = converse eqs" using trans_ish by blast
  lemma trans_part_3[intro]:"(a', b') \<in> eqs \<Longrightarrow> (a, b') \<in> eqs \<Longrightarrow> (a', b) \<in> eqs \<Longrightarrow> (a, b) \<in> eqs" 
    using trans_part_2 trans_ish by blast
  lemma idempotent[intro]:"idempotent eqs_a" "idempotent eqs_b"
    by (auto simp:idempotent_def O_assoc)
  lemma trans[intro]:"trans eqs_a" "trans eqs_b" by (intro idempotent[THEN idempotent_impl_trans])+
  lemma eqs_equiv[intro]:
    "equiv (Domain eqs) eqs_a" "equiv (Range eqs) eqs_b" by (rule equivI,auto)+
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

locale valid_unification =
  fixes f
  assumes "\<And> eqs lhs rhs. variable_distinctness eqs lhs rhs \<Longrightarrow>
             (case f eqs lhs rhs of (nms_a,nms_b) \<Rightarrow> variable_unification eqs lhs rhs nms_a nms_b)"

lemma exI_partial:
  assumes "a \<in> X" "P a"
  shows "\<exists> a \<in> X. P a"
using assms by blast

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
      case 6
      then show ?case using disj by (auto elim!:cluster_dest cluster1 simp:univalent_def)
    next
      case 7
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