theory MissingRelation
imports Main
begin

lemma range_dom[simp]:
  "f `` Domain f = Range f"
  "converse f `` Range f = Domain f" by auto

lemma Gr_Image_is_image[simp]:
  shows "BNF_Def.Gr A f `` B = f ` (A \<inter> B)"
  unfolding BNF_Def.Gr_def by auto

definition univalent where "univalent R = (\<forall> x y z. (x,y)\<in> R \<and> (x,z)\<in> R \<longrightarrow> z = y)"

lemma univalent_inter[intro]:
  assumes "univalent f_a" "univalent f_b"
  shows "univalent (f_a \<inter> f_b)"
  using assms unfolding univalent_def by auto

lemma univalent_union[intro]:
  assumes "univalent f_a" "univalent f_b" "Domain f_a \<inter> Domain f_b = Domain (f_a \<inter> f_b)"
  shows "univalent (f_a \<union> f_b)"
  unfolding univalent_def
proof(clarify,rule ccontr)
  from assms have uni:"univalent (f_a \<inter> f_b)" by auto
  fix x y z
  assume a:"(x, y) \<in> f_a \<union> f_b" "(x, z) \<in> f_a \<union> f_b" "z \<noteq> y"
  show False 
  proof(cases "(x,y) \<in> f_a")
    case True
    hence fb:"(x,z)\<in>f_b" using a assms[unfolded univalent_def] by auto
    hence "x \<in> (Domain f_a \<inter> Domain f_b)" using True by auto
    with assms uni fb True have "z = y" by (metis DomainE IntD1 IntD2 univalent_def)
    with a show False by auto
  next
    case False
    hence fb:"(x,z)\<in>f_a" "(x,y) \<in> f_b" using a assms[unfolded univalent_def] by auto
    hence "x \<in> (Domain f_a \<inter> Domain f_b)" by auto
    with assms uni fb have "z = y" by (metis DomainE IntD1 IntD2 univalent_def)
    with a show False by auto
  qed
qed

lemma Gr_univalent[intro]:
  shows "univalent (BNF_Def.Gr A f)"
  unfolding BNF_Def.Gr_def univalent_def by auto

lemma Gr_domain[simp]:
  shows "Domain (BNF_Def.Gr A f) = A"
    and "Domain (BNF_Def.Gr A id O R) = A \<inter> Domain R" unfolding BNF_Def.Gr_def by auto

lemma in_Gr[simp]:
  shows "(x,y) \<in> BNF_Def.Gr A f \<longleftrightarrow> x \<in> A \<and> f x = y"
  unfolding BNF_Def.Gr_def by auto

lemma Id_on_domain[simp]:
  "Domain (Id_on A O f) = A \<inter> Domain f" by auto

lemma Id_on_int:
  "Id_on A O f = (A \<times> UNIV) \<inter> f" by auto

lemma Domain_int_univ:
  "Domain (A \<times> UNIV \<inter> f) = A \<inter> Domain f" by auto

lemma Gr_range[simp]:
  shows "Range (BNF_Def.Gr A f) = f ` A" unfolding BNF_Def.Gr_def by auto

lemma tuple_disj[simp]:
  shows "{y. y = x \<or> y = z} = {x,z}" by auto

lemma univalent_empty [intro]: "univalent {}" unfolding univalent_def by auto

lemma univalent_char : "univalent R \<longleftrightarrow> converse R O R \<subseteq> Id"
  unfolding univalent_def by auto

lemma univalentD [dest]: "univalent R \<Longrightarrow> (x,y)\<in> R \<Longrightarrow> (x,z)\<in> R \<Longrightarrow> z = y"
  unfolding univalent_def by auto

lemma univalentI: "converse R O R \<subseteq> Id \<Longrightarrow> univalent R"
  unfolding univalent_def by auto

lemma univalent_composes[intro]:assumes "univalent R" "univalent S"
 shows "univalent (R O S)" using assms unfolding univalent_char by auto

lemma id_univalent[intro]:"univalent (Id_on x)" unfolding univalent_char by auto

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
    show "x \<in> A \<Longrightarrow> (x, x) \<in> r\<^sup>+" for x
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

end