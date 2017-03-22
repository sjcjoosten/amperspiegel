theory VariableUnification
imports
  Main
begin

locale variable_unification =
  fixes eqs :: "('a \<times> 'b) set"
    and lhs :: "'a set"
    and rhs :: "'b set"
    and nms_a :: "('a \<times> 'c) set"
    and nms_b :: "('b \<times> 'c) set"
  assumes eqs:"nms_a O converse nms_b = eqs"
      and dom:"lhs \<subseteq> Domain nms_a"
      and ran:"rhs \<subseteq> Domain nms_b"
      and inj_a:"\<And> a c a'. a \<in> lhs \<Longrightarrow> a' \<in> lhs \<Longrightarrow> (a,c) \<in> nms_a \<Longrightarrow> (a',c) \<in> nms_a \<Longrightarrow> a = a'"
      and inj_b:"\<And> a c a'. a \<in> rhs \<Longrightarrow> a' \<in> rhs \<Longrightarrow> (a,c) \<in> nms_b \<Longrightarrow> (a',c) \<in> nms_b \<Longrightarrow> a = a'"
      and uni_a:"\<And> a c c'. (a,c) \<in> nms_a \<Longrightarrow> (a,c') \<in> nms_a \<Longrightarrow> c = c'"
      and uni_b:"\<And> a c c'. (a,c) \<in> nms_b \<Longrightarrow> (a,c') \<in> nms_b \<Longrightarrow> c = c'"
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

definition idempotent where
  "idempotent r \<equiv> r O r = r"

lemma trans_def: "trans r = ((Id \<union> r) O r = r)" "trans r = (r O (Id \<union> r) = r)"
  by(auto simp:trans_def)

lemma idempotent_impl_trans: "idempotent r \<Longrightarrow> trans r"
  by(auto simp:trans_def idempotent_def)

definition cluster :: "('a \<times> 'b) set \<Rightarrow> (('a \<times> 'b) \<times> ('a \<times> 'b) set) set" where
  "cluster R \<equiv> (\<lambda> p. (p,{e \<in> R . fst e = fst p \<or> snd e = snd p})) ` R"

lemma cluster_dest:
  assumes "((a', b'), S) \<in> cluster eqs"
  shows "(a',b') \<in> eqs" "S = {(a,b) \<in> eqs . a = a'} \<union> {(a,b) \<in> eqs . b = b'}"
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
  lemma idempotent[intro]:"idempotent eqs_a" "idempotent eqs_b"
    by (auto simp:idempotent_def O_assoc)
  lemma trans[intro]:"trans eqs_a" "trans eqs_b" by (intro idempotent[THEN idempotent_impl_trans])+
  lemma eqs_equiv[intro]:
    "equiv (Domain eqs) eqs_a" "equiv (Range eqs) eqs_b" by (rule equivI,auto)+
  lemma cluster1:
    assumes "((a,b1),c1) \<in> cluster eqs" "((a,b2),c2) \<in> cluster eqs"
    shows "c1 = c2" sorry
  lemma cluster2:
    assumes "((b1,a),c1) \<in> cluster eqs" "((b2,a),c2) \<in> cluster eqs"
    shows "c1 = c2" sorry
  lemma cluster3:
    assumes "((aa, ba), bd) \<in> cluster eqs" "((ab, bc), bd) \<in> cluster eqs"
    shows "(aa, bc) \<in> eqs" sorry
  lemma cluster4:
    assumes "x \<in> eqs"
    shows "(x, {e \<in> eqs . fst e = fst x \<or> snd e = snd x}) \<in> cluster eqs"
    using assms unfolding cluster_def by auto
end

locale valid_unification =
  fixes f
  assumes "\<And> eqs lhs rhs. variable_distinctness eqs lhs rhs \<Longrightarrow>
             (case f eqs lhs rhs of (nms_a,nms_b) \<Rightarrow> variable_unification eqs lhs rhs nms_a nms_b)"

lemma exI_partial:
  assumes "a \<in> X" "P a"
  shows "\<exists> a \<in> X. P a"
using assms by blast

datatype ('a,'b) freenaming = L 'a | R 'b  | P "('a \<times> 'b) set"
definition freename :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> ('a, 'b) freenaming) set \<times> ('b \<times> ('a, 'b) freenaming) set" 
  where "freename eqs lhs rhs = ( (\<lambda> ((a,b),c). (a,P c)) ` cluster eqs \<union> (\<lambda> a. (a,L a)) ` lhs
                                , (\<lambda> ((a,b),c). (b,P c)) ` cluster eqs \<union> (\<lambda> a. (a,R a)) ` rhs )"
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
          with cluster4[OF 2] have e:"(x, {e \<in> eqs. fst e = xa \<or> snd e = z}) \<in> cluster eqs" by auto
          let "?y" = "P {e \<in> eqs. fst e = xa \<or> snd e = z}"
          have "\<exists>x'\<in>cluster eqs. \<forall>a b x2. x' = ((a, b), x2) \<longrightarrow> xa = a \<and> ?y = P x2"
               "\<exists>x'\<in>cluster eqs. \<forall>a b x2. x' = ((a, b), x2) \<longrightarrow> z = b \<and> ?y = P x2"
            using e a by (metis (no_types, lifting) Pair_inject prod.case)+
        } note [intro] = this
        hence i:"x \<in> ((\<lambda>((a, b), c). (a, P c)) ` cluster eqs O ((\<lambda>((a, b), c). (b, P c)) ` cluster eqs)\<inverse>)"
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
      case (6 a c c')
      then show ?case using disj by (auto elim!:cluster_dest cluster1)
    next
      case (7 a c c')
      then show ?case using disj by (auto elim!:cluster_dest cluster2)
    qed auto
  qed


end