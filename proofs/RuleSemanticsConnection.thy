theory RuleSemanticsConnection
imports LabeledGraphSemantics RulesAndChains
begin

(* gets the top relation-label as argument *)
definition top_rule :: "'l \<Rightarrow> ('l,'v::{one,zero,numeral}) Graph_PreRule" where
"top_rule t = (LG {} {0,1},LG {(t,0,1)} {0,1})"

definition nonempty_rule :: "('l,'v::{one,zero,numeral}) Graph_PreRule" where
"nonempty_rule = (LG {} {},LG {} {0})"

(* gets a reflexive relation-label as argument *)
definition reflexivity_rule :: "'l \<Rightarrow> ('l,'v::{one,zero,numeral}) Graph_PreRule" where
"reflexivity_rule t = (LG {} {0},LG {(t,0,0)} {0})"

lemma are_rules[intro]:
"graph_rule nonempty_rule"
"graph_rule (top_rule t)"
"graph_rule (reflexivity_rule i)"
  unfolding reflexivity_rule_def top_rule_def nonempty_rule_def is_graph_homomorphism_def
  by auto

fun translation :: "'c allegorical_term \<Rightarrow> ('c, nat) labeled_graph" where
"translation (A_Lbl l) = LG {(l,0,1)} {0,1}" |
"translation (A_Cnv e) = map_graph_fn (translation e) (\<lambda> x. if x<2 then (1-x) else x)" |
"translation (A_Cmp e\<^sub>1 e\<^sub>2)
  = (let G\<^sub>1 = translation e\<^sub>1 ; G\<^sub>2 = translation e\<^sub>2
     in graph_union (map_graph_fn G\<^sub>1 (\<lambda> x. if x=0 then 0 else x+card(vertices G\<^sub>2)-1))
                    (map_graph_fn G\<^sub>2 (\<lambda> x. if x=0 then card (vertices G\<^sub>2) else x)))" |
"translation (A_Int e\<^sub>1 e\<^sub>2)
  = (let G\<^sub>1 = translation e\<^sub>1 ; G\<^sub>2 = translation e\<^sub>2
     in graph_union G\<^sub>1 (map_graph_fn G\<^sub>2 (\<lambda> x. if x<2 then x else x+card(vertices G\<^sub>1)-2)))"

definition inv_translation where
"inv_translation r \<equiv> {0..<card r} = r \<and> {0,1}\<subseteq>r"

lemma inv_translationI4[intro]:
  assumes "finite r" "\<And> x. x < card r \<Longrightarrow> x \<in> r"
  shows "r={0..<card r}"
proof(insert assms,induct "card r" arbitrary:r)
  case (Suc x r)
  let ?r = "r - {x}"
  from Suc have p:"x = card ?r" "finite ?r" by auto
  have p2:"xa < card ?r \<Longrightarrow> xa \<in> ?r" for xa
    using Suc.prems(2)[of xa] Suc.hyps(2) unfolding p(1)[symmetric] by auto
  from Suc.hyps(1)[OF p p2] have "?r={0..<card ?r}".
  with Suc.hyps(2) Suc.prems(1) show ?case
    by (metis atLeast0_lessThan_Suc card_Diff_singleton_if insert_Diff n_not_Suc_n p(1))
qed auto

lemma inv_translationI[intro!]:
assumes "finite r" "\<And> x. x < card r \<Longrightarrow> x \<in> r" "0 \<in> r" "Suc 0 \<in> r"
shows "inv_translation r"
proof -
  from inv_translationI4[OF assms(1,2),symmetric]
  have c:" {0..<card r} = r " by auto
  from assms(3,4) have "{0,1} \<subseteq> r" by auto
  with c inv_translation_def show ?thesis by auto
qed

lemma verts_in_translation_finite[intro]:
"finite (vertices (translation X))"
"finite (edges (translation X))"
"0 \<in> vertices (translation X)"
"Suc 0 \<in> vertices (translation X)"
proof(atomize(full),induction X)
  case (A_Int X1 X2)
  then show ?case by (auto simp:Let_def)
next
  case (A_Cmp X1 X2)
  then show ?case by (auto simp:Let_def)
next
  have [simp]:"{x::nat. x < 2} = {0,1}" by auto
  case (A_Cnv X)
  then show ?case by auto
qed auto

lemma inv_tr_card_min:
  assumes "inv_translation r"
  shows "card r \<ge> 2" 
proof -
  note [simp] = inv_translation_def
  have "{0..<x} = r \<Longrightarrow> 2 \<le> x \<longleftrightarrow> 0 \<in> r \<and> 1 \<in> r" for x by auto
  thus ge2:"card r\<ge>2" using assms by auto
qed

lemma verts_in_translation[intro]:
"inv_translation (vertices (translation X))"
proof(induct X)
  { fix r
    assume assms:"inv_translation r"
    note [simp] = inv_translation_def
    from assms have a1:"finite r"
      by (intro card_ge_0_finite) auto
    have [simp]:"{0..<Suc x} = {0..<x} \<union> {x}" for x by auto
    note ge2 = inv_tr_card_min[OF assms]
    from ge2 assms have r0:"r \<inter> {0} = {0}" "r \<inter> {x. x < 2} = {0,1}" by auto
    have [intro!]:"\<And>x. x \<in> r \<Longrightarrow> x < card r"
     and g6:"\<And>x. x < card r \<longleftrightarrow> x \<in> r"
      using assms[unfolded inv_translation_def] atLeastLessThan_iff by blast+
    have g4:"r \<inter> {x. \<not> x < 2} = {2..<card r}"
            "r \<inter> (Collect ((<) 0)) = {1..<card r}" using assms by fastforce+
    have ins:"1 \<in> r" "0 \<in> r" using assms by auto
    have d:"Suc (Suc (card r - 2)) = card r"
      using ge2 One_nat_def Suc_diff_Suc Suc_pred 
            numeral_2_eq_2 by presburger
    note ge2 ins g4 g6 r0 d
  } note inv_translationD[simp] = this
  {
    fix a b c
    assume assm:"b \<le> (a::nat)"
    have "(\<lambda>x. x + a - b) ` {b..<c} = {a..<c+a-b}" (is "?lhs = ?rhs")
    proof -
      from assm have "?lhs = (\<lambda>x. x + (a - b)) ` {b..<c}" by auto
      also have "\<dots> = ?rhs" 
        unfolding linordered_semidom_class.image_add_atLeastLessThan' using assm by auto
      finally show ?thesis by auto
    qed
  } note e[simp] = this
  { fix r z
    assume a1: "inv_translation z" and a2: "inv_translation r"
    let ?z2 = "card z + card r - 2"
    let ?z1 = "card z + card r - Suc 0"
    from a1 a2
    have le1:"Suc 0 \<le> card r"
      by (metis Suc_leD inv_translationD(1) numerals(2))
    hence le2: "card r \<le> ?z1"
      by (metis Suc_leD a1 inv_translationD(1) numerals(2) ordered_cancel_comm_monoid_diff_class.le_add_diff)
    with le1 have b:"{card r ..< ?z1} \<union> {Suc 0 ..< card r} = {Suc 0 ..< ?z1}"
      by auto
    have a:"(insert (card r) {0..<card z + card r - Suc 0}) = {0..<card z + card r - Suc 0}"
      using le1 le2 a1 a2
      by (metis Suc_leD add_Suc_right atLeastLessThan_iff diff_Suc_Suc insert_absorb inv_translationD(1) linorder_not_less not_less_eq_eq numerals(2) ordered_cancel_comm_monoid_diff_class.le_add_diff)
    from a1 a2
    have "card z + card r - 2 \<ge> card (r::nat set)"
      by (simp add: ordered_cancel_comm_monoid_diff_class.le_add_diff)
    with a2
    have c:"card (r \<union> {card r..<?z2}) = ?z2"
      by (metis atLeast0LessThan card_atLeastLessThan diff_zero inv_translation_def ivl_disj_un_one(2))+
    note a b c
  } note [simp] = this
  have [simp]:"a < x \<Longrightarrow> insert a {Suc a..<x} = {a..<x}" for a x by auto
  { case (A_Int X1 X2)
    let ?v1 = "vertices (translation X1)"
    from A_Int have [simp]:"(insert 0 (insert (Suc 0) (?v1 \<union> x))) = ?v1 \<union> x"
      for x unfolding inv_translation_def by auto
    from A_Int show ?case by (auto simp:Let_def linorder_not_le)
  next
    case (A_Cmp X1 X2)
    hence "2\<le>card (vertices (translation X1))" "2\<le>card (vertices (translation X2))" by auto
    hence "1 \<le>card (vertices (translation X1))" "1\<le>card (vertices (translation X2))"
          "1 < card (vertices (translation X1)) + card (vertices (translation X2)) - 1"
      by auto
    from this A_Cmp
    show ?case by (auto simp:Let_def)
  next
    case (A_Cnv X)
    thus ?case by (auto simp:Let_def)
  }
qed auto

lemma translation_graph[intro]:
"graph (translation X)"
  by (induct X, auto simp:Let_def)

lemma graph_rule_translation[intro]: (* remark at the end of Def 15 *)
"graph_rule (translation X, translation (A_Int X Y))"
  using verts_in_translation_finite[of X] verts_in_translation_finite[of "A_Int X Y"]
        translation_graph[of X] translation_graph[of "A_Int X Y"]
  by (auto simp:Let_def subgraph_def2)

lemma translation: (* Lemma 5 *)
  assumes "graph G"
  shows "(x, y) \<in> :G:\<lbrakk>e\<rbrakk> \<longleftrightarrow> (\<exists> f. is_graph_homomorphism (translation e) G f \<and> (0,x) \<in> f \<and> (1,y) \<in> f)"
(is "?lhs = ?rhs")
proof
  have [dest]:"y + card (vertices (translation (e::'a allegorical_term))) - 2 < 2 \<Longrightarrow> (y::nat) < 2"
    for y e using inv_tr_card_min[OF verts_in_translation,of e] by linarith
  {  fix y fix e::"'a allegorical_term"
     assume "y + card (vertices (translation e)) - 2 \<in> vertices (translation e)"
     hence "y + card (vertices (translation e)) - 2 < card (vertices (translation e))"
       using verts_in_translation[of e,unfolded inv_translation_def] by auto
     hence "y < 2" using inv_tr_card_min[OF verts_in_translation,of e] by auto
  } note [dest!] = this
  {  fix y fix e::"'a allegorical_term"
     assume "y + card (vertices (translation e)) - Suc 0 \<in> vertices (translation e)"
     hence "y + card (vertices (translation e)) - Suc 0 \<in> {0..<card (vertices (translation e))}"
       using verts_in_translation[of e,unfolded inv_translation_def] by simp
     hence "y = 0" using inv_tr_card_min[OF verts_in_translation,of e] by auto
   } note [dest!] = this
   {  fix y fix e::"'a allegorical_term"
     assume "card (vertices (translation e)) \<in> vertices (translation e)"
     hence "card (vertices (translation e)) \<in> {0..<card (vertices (translation e))}"
       using verts_in_translation[of e,unfolded inv_translation_def] by auto
     hence "False" by auto
   } note [dest!] = this
  {  fix y fix e::"'a allegorical_term"
     assume "y + card (vertices (translation e)) \<le> Suc 0"
     hence " card (vertices (translation e)) \<le> Suc 0" by auto
     hence "False" using inv_tr_card_min[OF verts_in_translation[of e]] by auto
   } note [dest!] = this
  assume ?lhs
  then show ?rhs
  proof(induct e arbitrary:x y)
    case (A_Int e\<^sub>1 e\<^sub>2)
    from A_Int have assm:"(x, y) \<in> :G:\<lbrakk>e\<^sub>1\<rbrakk>" "(x, y) \<in> :G:\<lbrakk>e\<^sub>2\<rbrakk>" by auto
    from A_Int(1)[OF assm(1)] obtain f\<^sub>1 where
      f\<^sub>1:"is_graph_homomorphism (translation e\<^sub>1) G f\<^sub>1" "(0, x) \<in> f\<^sub>1" "(1, y) \<in> f\<^sub>1" by auto
    from A_Int(2)[OF assm(2)] obtain f\<^sub>2 where
      f\<^sub>2:"is_graph_homomorphism (translation e\<^sub>2) G f\<^sub>2" "(0, x) \<in> f\<^sub>2" "(1, y) \<in> f\<^sub>2" by auto
    from f\<^sub>1 f\<^sub>2 have v:"Domain f\<^sub>1 = vertices (translation e\<^sub>1)" "Domain f\<^sub>2 = vertices (translation e\<^sub>2)"
      unfolding is_graph_homomorphism_def by auto
    let ?f\<^sub>2 = "(\<lambda> x. if x < 2 then x else x + card (vertices (translation e\<^sub>1)) - 2)"
    let ?tr\<^sub>2 = "on_graph (translation e\<^sub>2) ?f\<^sub>2"
    have inj2:"inj_on ?f\<^sub>2 (vertices (translation e\<^sub>2))" unfolding inj_on_def by auto
    have "(0,0) \<in> ?tr\<^sub>2\<inverse>" "(1,1) \<in> ?tr\<^sub>2\<inverse>" by auto
    from this[THEN relcompI] f\<^sub>2(2,3) 
    have zero_one:"(0,x) \<in> ?tr\<^sub>2\<inverse> O f\<^sub>2"
                  "(1,y) \<in> ?tr\<^sub>2\<inverse> O f\<^sub>2" by auto
    { fix yb zb
      assume "(yb + card (vertices (translation e\<^sub>1)) - 2, zb) \<in> f\<^sub>1"
      hence "yb + card (vertices (translation e\<^sub>1)) - 2 \<in> vertices (translation e\<^sub>1)" using v by auto
    } note in_f[dest!] = this
    have d_a:"Domain f\<^sub>1 \<inter>  Domain (?tr\<^sub>2\<inverse> O f\<^sub>2) = {0,1}"
      using zero_one by (auto simp:v)
    have d_b:"Domain (f\<^sub>1 \<inter> ?tr\<^sub>2\<inverse> O f\<^sub>2) = {0,1}"
      using zero_one f\<^sub>1(2,3) by auto
    note cmp2 = is_graph_homomorphism_composes[OF graph_homo_inv[OF translation_graph inj2] f\<^sub>2(1)]
    have "is_graph_homomorphism (translation (A_Int e\<^sub>1 e\<^sub>2)) G (f\<^sub>1 \<union> ?tr\<^sub>2\<inverse> O f\<^sub>2)"
      using graph_homo_union[OF f\<^sub>1(1) cmp2 d_a[folded d_b]]
      by (auto simp:Let_def)
    thus ?case using zero_one[THEN UnI2[of _ _ "f\<^sub>1"]] by blast
  next
    case (A_Cmp e\<^sub>1 e\<^sub>2)
    from A_Cmp obtain z where assm:"(x, z) \<in> :G:\<lbrakk>e\<^sub>1\<rbrakk>" "(z, y) \<in> :G:\<lbrakk>e\<^sub>2\<rbrakk>" by auto
    from A_Cmp(1)[OF assm(1)] obtain f\<^sub>1 where
      f\<^sub>1:"is_graph_homomorphism (translation e\<^sub>1) G f\<^sub>1" "(0, x) \<in> f\<^sub>1" "(1, z) \<in> f\<^sub>1" by auto
    from A_Cmp(2)[OF assm(2)] obtain f\<^sub>2 where
      f\<^sub>2:"is_graph_homomorphism (translation e\<^sub>2) G f\<^sub>2" "(0, z) \<in> f\<^sub>2" "(1, y) \<in> f\<^sub>2" by auto
    from f\<^sub>1 f\<^sub>2 have v:"Domain f\<^sub>1 = vertices (translation e\<^sub>1)" "Domain f\<^sub>2 = vertices (translation e\<^sub>2)"
      unfolding is_graph_homomorphism_def by auto
    let ?f\<^sub>1 = "(\<lambda> x. if x=0 then 0 else x+card(vertices (translation e\<^sub>2))-1)"
    let ?f\<^sub>2 = "(\<lambda> x. if x=0 then card (vertices (translation e\<^sub>2)) else x)"
    let ?tr\<^sub>1 = "on_graph (translation e\<^sub>1) ?f\<^sub>1"
    let ?tr\<^sub>2 = "on_graph (translation e\<^sub>2) ?f\<^sub>2"
    have inj1:"inj_on ?f\<^sub>1 (vertices (translation e\<^sub>1))" unfolding inj_on_def by auto
    have inj2:"inj_on ?f\<^sub>2 (vertices (translation e\<^sub>2))" unfolding inj_on_def by auto
    have "(card (vertices (translation e\<^sub>2)),0) \<in> ?tr\<^sub>2\<inverse>" "(1,1) \<in> ?tr\<^sub>2\<inverse>"
         "(0,0) \<in> ?tr\<^sub>1\<inverse>" "(card (vertices (translation e\<^sub>2)),1) \<in> ?tr\<^sub>1\<inverse>" by auto
    from this[THEN relcompI] f\<^sub>2(2,3) f\<^sub>1(2,3) 
    have zero_one:"(card (vertices (translation e\<^sub>2)),z) \<in> ?tr\<^sub>1\<inverse> O f\<^sub>1"
                  "(0,x) \<in> ?tr\<^sub>1\<inverse> O f\<^sub>1"
                  "(card (vertices (translation e\<^sub>2)),z) \<in> ?tr\<^sub>2\<inverse> O f\<^sub>2"
                  "(1,y) \<in> ?tr\<^sub>2\<inverse> O f\<^sub>2" by auto
    have [simp]:
        "ye \<in> vertices (translation e\<^sub>2) \<Longrightarrow>
       (if ye = 0 then card (vertices (translation e\<^sub>2)) else ye) =
       (if yd = 0 then 0 else yd + card (vertices (translation e\<^sub>2)) - 1) \<longleftrightarrow> ye = 0 \<and> yd = 1"
        for ye yd using v inv_tr_card_min[OF verts_in_translation,of "e\<^sub>2"]
        by(cases "ye=0";cases "yd=0";auto)
    have d_a:"Domain (?tr\<^sub>1\<inverse> O f\<^sub>1) \<inter>  Domain (?tr\<^sub>2\<inverse> O f\<^sub>2) = {card (vertices (translation e\<^sub>2))}"
      using zero_one by (auto simp:v)
    have d_b:"Domain (?tr\<^sub>1\<inverse> O f\<^sub>1 \<inter> ?tr\<^sub>2\<inverse> O f\<^sub>2) = {card (vertices (translation e\<^sub>2))}"
      using zero_one f\<^sub>1(2,3) by auto
    note cmp1 = is_graph_homomorphism_composes[OF graph_homo_inv[OF translation_graph inj1] f\<^sub>1(1)]
    note cmp2 = is_graph_homomorphism_composes[OF graph_homo_inv[OF translation_graph inj2] f\<^sub>2(1)]
    have "is_graph_homomorphism (translation (A_Cmp e\<^sub>1 e\<^sub>2)) G (?tr\<^sub>1\<inverse> O f\<^sub>1 \<union> ?tr\<^sub>2\<inverse> O f\<^sub>2)"
      unfolding Let_def translation.simps
      by (rule graph_homo_union[OF cmp1 cmp2 d_a[folded d_b]])
    thus ?case using zero_one by blast
  next
    case (A_Cnv e)
    let ?G = "translation (A_Cnv e)"
    from A_Cnv obtain f where
      f:"is_graph_homomorphism (translation e) G f" "(0, y) \<in> f" "(1, x) \<in> f" by auto
    hence v:"Domain f = vertices (translation e)"
      unfolding is_graph_homomorphism_def by auto
    define n where "n \<equiv> card (vertices (translation e))"
    from verts_in_translation f inv_tr_card_min[OF verts_in_translation] v(1)
    have n:"vertices (translation e) = {0..<n}" "{0..<n} \<inter> {x. x < 2} = {1,0}"
      "Domain f = {0..<n}" "{0..<n} \<inter> {x. \<not> x < 2} = {2..<n}"
      and n2: "n \<ge> 2"
      by (auto simp:n_def inv_translation_def)
    then have [simp]:"insert (Suc 0) {2..<n} = {1..<n}"
      "insert 0 {Suc 0..<n} = {0..<n}" by auto
    let ?f = "on_graph ?G (\<lambda> x. if x < 2 then 1 - x else x)"
    have h:"is_graph_homomorphism ?G G (?f O f)"
    proof(rule is_graph_homomorphism_composes[OF _ f(1)],standard)
      show "vertices ?G = Domain ?f"
        by (auto simp:Domain_int_univ)
      show "?f `` vertices ?G \<subseteq> vertices (translation e)" using n2 by auto
      show "univalent ?f" by auto
      show "edge_preserving ?f (edges (translation (A_Cnv e))) (edges (translation e))"
        by (rule edge_preserving_on_graphI,auto simp: BNF_Def.Gr_def)
    qed (auto intro:assms)
    have xy:"(0, x) \<in> ?f O f" "(1, y) \<in> ?f O f" using n2 f(2,3) n(1,2) by auto
    with h show ?case by auto
  next
    case (A_Lbl l)
    let ?f = "{(0,x),(1,y)}"
    have xy:"x \<in> vertices G" "y \<in> vertices G" using assms A_Lbl by (auto simp:getRel_def)
    have "is_graph_homomorphism (translation (A_Lbl l)) G ?f \<and> (0, x) \<in> ?f \<and> (1, y) \<in> ?f"
      using assms A_Lbl xy unfolding is_graph_homomorphism_def2
      by (auto simp:univalent_def getRel_def on_triple_def Image_def graph_union_def insert_absorb)
    then show ?case by auto
  qed
next
  assume ?rhs
  then obtain f where
    f:"is_graph_homomorphism (translation e) G f" "(0, x) \<in> f" "(1, y) \<in> f" by blast
  thus ?lhs
  proof(induct e arbitrary:f x y)
  case (A_Int e\<^sub>1 e\<^sub>2 f x y)
    let ?f\<^sub>1 = "id"
    let ?f\<^sub>2 = "(\<lambda> x. if x < 2 then x else x + card (vertices (translation e\<^sub>1)) - 2)"
    let ?G\<^sub>1 = "translation e\<^sub>1"
    let ?G\<^sub>2 = "translation e\<^sub>2"
    have f1:"(0, x) \<in> on_graph ?G\<^sub>1 ?f\<^sub>1 O f" "(1, y) \<in> on_graph ?G\<^sub>1 ?f\<^sub>1 O f"
     and f2:"(0, x) \<in> on_graph ?G\<^sub>2 ?f\<^sub>2 O f" "(1, y) \<in> on_graph ?G\<^sub>2 ?f\<^sub>2 O f"
      using A_Int.prems(2,3) by (auto simp:BNF_Def.Gr_def relcomp_def)
    from A_Int.prems(1)
    have uni:"is_graph_homomorphism (graph_union ?G\<^sub>1 (map_graph_fn ?G\<^sub>2 ?f\<^sub>2)) G f"
      by (auto simp:Let_def)
    from graph_homo_union_id(1)[OF uni translation_graph]
    have h1:"is_graph_homomorphism ?G\<^sub>1 (translation (A_Int e\<^sub>1 e\<^sub>2)) (on_graph ?G\<^sub>1 id)"
      by (auto simp:Let_def is_graph_homomorphism_def)
    have "graph (map_graph_fn ?G\<^sub>2 ?f\<^sub>2)" by auto
    from graph_homo_union_id(2)[OF uni this]
    have h2:"is_graph_homomorphism ?G\<^sub>2 (translation (A_Int e\<^sub>1 e\<^sub>2)) (on_graph ?G\<^sub>2 ?f\<^sub>2)"
      by (auto simp:Let_def is_graph_homomorphism_def)
    from A_Int.hyps(1)[OF is_graph_homomorphism_composes[OF h1 A_Int.prems(1)] f1]
         A_Int.hyps(2)[OF is_graph_homomorphism_composes[OF h2 A_Int.prems(1)] f2]
    show ?case by auto
  next
    case (A_Cmp e\<^sub>1 e\<^sub>2 f x y)
    let ?f\<^sub>1 =  "(\<lambda> x. if x=0 then 0 else x+card(vertices (translation e\<^sub>2))-1)"
    let ?f\<^sub>2 =  "(\<lambda> x. if x=0 then card (vertices (translation e\<^sub>2)) else x)" 
    let ?G\<^sub>1 = "translation e\<^sub>1"
    let ?G\<^sub>2 = "translation e\<^sub>2"
    let ?v = "card (vertices (translation e\<^sub>2))"
    from A_Cmp.prems(1) have "?v \<in> Domain f" by (auto simp:Let_def is_graph_homomorphism_def)
    then obtain v where v:"(?v,v) \<in> f" by auto
    have f1:"(0, x) \<in> on_graph ?G\<^sub>1 ?f\<^sub>1 O f" "(1, v) \<in> on_graph ?G\<^sub>1 ?f\<^sub>1 O f"
     and f2:"(0, v) \<in> on_graph ?G\<^sub>2 ?f\<^sub>2 O f" "(1, y) \<in> on_graph ?G\<^sub>2 ?f\<^sub>2 O f"
      using A_Cmp.prems(2,3) v by auto
    from A_Cmp.prems(1)
    have uni:"is_graph_homomorphism (graph_union (map_graph_fn ?G\<^sub>1 ?f\<^sub>1) (map_graph_fn ?G\<^sub>2 ?f\<^sub>2)) G f"
      by (auto simp:Let_def)
    have "graph (map_graph_fn ?G\<^sub>1 ?f\<^sub>1)" by auto
    from graph_homo_union_id(1)[OF uni this]
    have h1:"is_graph_homomorphism ?G\<^sub>1 (translation (A_Cmp e\<^sub>1 e\<^sub>2)) (on_graph ?G\<^sub>1 ?f\<^sub>1)"
      by (auto simp:Let_def is_graph_homomorphism_def2)
    have "graph (map_graph_fn ?G\<^sub>2 ?f\<^sub>2)" by auto
    from graph_homo_union_id(2)[OF uni this]
    have h2:"is_graph_homomorphism ?G\<^sub>2 (translation (A_Cmp e\<^sub>1 e\<^sub>2)) (on_graph ?G\<^sub>2 ?f\<^sub>2)"
      by (auto simp:Let_def is_graph_homomorphism_def2)
    from A_Cmp.hyps(1)[OF is_graph_homomorphism_composes[OF h1 A_Cmp.prems(1)] f1]
         A_Cmp.hyps(2)[OF is_graph_homomorphism_composes[OF h2 A_Cmp.prems(1)] f2]
    show ?case by auto
  next
    case (A_Cnv e f x y)
    let ?f = "(\<lambda> x. if x < 2 then 1 - x else x)"
    let ?G = "translation e"
    have i:"is_graph_homomorphism ?G (map_graph_fn ?G ?f) (on_graph ?G ?f)" using A_Cnv by auto
    have "(0, y) \<in> on_graph ?G ?f O f" "(1, x) \<in> on_graph ?G ?f O f"
      using A_Cnv.prems(3,2) by (auto simp:BNF_Def.Gr_def relcomp_def)
    from A_Cnv.hyps(1)[OF is_graph_homomorphism_composes[OF i] this] A_Cnv.prems(1)
    show ?case by auto
  next
  case (A_Lbl l f x y)
    hence "edge_preserving f {(l,0,1)} (edges G)" unfolding is_graph_homomorphism_def by auto
    with A_Lbl(2,3) show ?case by (auto simp:getRel_def edge_preserving_def)
  qed
qed

(* Work towards Lemma 6 and 7 *)
end