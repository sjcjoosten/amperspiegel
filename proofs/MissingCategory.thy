theory MissingCategory
imports
  Limit
begin

section {* MissingCategory: Category theory preliminaries *}

text {*
  MissingCategory is a wrapper for the Category3 AFP entry.
  Its aim is to make the Category locale easier to use.
  First, we provide the locale ArrowCategory that will make it even easier to create instances.
  Second, this is where we keep our own generic theorems about categories.

  To make it easier to create instances, we fix a datatype for morphisms in the category.
  This provides generic implementations for what all categories share:
    Finding domain and codomain of an arrow correctly.
    Determining whether two arrows are composable through domain and codomain.
  In addition, we implement our own preference to work with (compose f g) = g \<circ> f

  One of the generic facts about categories, is that every category has an opposite.
  ArrowCategory instantiates both: that of the category and its opposite.

  Those familiar with the Category3 AFP entry, it might be 
  The ArrowCategory locale follows the intuition behind the classical_category.

*}
datatype ('o,'m) Arrow = Arrow (source: 'o) (target: 'o) (morphism: 'm)
fun opA where
"opA (Arrow s t m) = Arrow t s m"

locale ArrowCategory =
  fixes valid_arrow :: "'o \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> bool"
    and valid_object :: "'o \<Rightarrow> bool"
    and cmp :: "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm"
    and identity :: "'o \<Rightarrow> 'm"
  assumes cmp_associative[intro]:
    "valid_arrow a b x \<Longrightarrow> valid_arrow b c y  \<Longrightarrow> valid_arrow c d z \<Longrightarrow>
     cmp a b d x (cmp b c d y z) = cmp a c d (cmp a b c x y) z"
  and cmp_valid[intro]:
     "valid_arrow a b x \<Longrightarrow> valid_arrow b c y \<Longrightarrow> valid_arrow a c (cmp a b c x y)"
  and identity_valid[intro]:
     "valid_object a \<Longrightarrow> valid_arrow a a (identity a)"
  and identity_left[simp]:
     "valid_arrow a b f \<Longrightarrow> cmp a a b (identity a) f = f"
  and identity_right[simp]:
     "valid_arrow a b f \<Longrightarrow> cmp a b b f (identity b) = f"
begin

abbreviation Arr :: "('o,'m) Arrow \<Rightarrow> bool" where
"Arr a \<equiv> (case a of Arrow s t m \<Rightarrow> valid_object s \<and> valid_object t \<and> valid_arrow s t m)"
abbreviation ID :: "'o \<Rightarrow> ('o,'m) Arrow" where "ID a \<equiv> Arrow a a (identity a)"
abbreviation Comp :: "('o,'m) Arrow \<Rightarrow> ('o,'m) Arrow \<Rightarrow> ('o,'m) Arrow" where
"Comp y x \<equiv> Arrow (source x) (target y) (cmp (source x) (target x) (target y) (morphism x) (morphism y))"

sublocale c : classical_category valid_object Arr source target ID Comp
  by (unfold_locales,auto split:Arrow.split_asm)
sublocale op : classical_category valid_object Arr target source ID "\<lambda> y x. Comp x y"
  using cmp_associative by (unfold_locales,auto split:Arrow.split_asm)
sublocale op_c: category op.comp using op.category_axioms.
sublocale c_c: category c.comp using c.category_axioms.

abbreviation "C x y \<equiv> c.comp y x"
lemma op_is_op : "C x y = op.comp x y" by (auto simp: "c.comp_def" "op.comp_def")

abbreviation "arr s t m \<equiv> Some (Arrow s t m)"

definition iso where "iso s t \<equiv> (\<exists> m. c.iso (arr s t m))"

lemma has_dom_cod_arrI[intro]:
  assumes "valid_object (source a)" "valid_object (target a)"
          "valid_arrow (source a) (target a) (morphism a)"
  shows "c.has_dom (Some a)"
        "c.has_cod (Some a)"
        "c.arr (Some a)"
proof -
  obtain s t m where a:"a = Arrow s t m" by (cases a)
  have h:"C (Some (Arrow s t m)) (Some (ID t)) \<noteq> None"
         "C (Some (ID s)) (Some (Arrow s t m)) \<noteq> None"
    unfolding c.comp_def using assms[unfolded a] by auto
  show "c.has_dom (Some a)" unfolding c.has_dom_def using h
    by auto (auto simp:c.null_char a intro!:c.unit_Some_Id[OF assms(1)])
  show "c.has_cod (Some a)" unfolding c.has_cod_def using h
    by auto (auto simp:c.null_char a intro!:c.unit_Some_Id[OF assms(2)])
  thus "c.arr (Some a)" unfolding a c.arr_def by blast
qed

lemma arr_dest[dest]:
  assumes "c.arr a"
  shows "Arr (the a)" "a = (Some (the a))"
  using assms[unfolded c.arr_char] by (auto split:Arrow.split simp:source_def target_def)

lemma Arr_dest[dest]:
  assumes "Arr a"
  shows "valid_object (target a)"
        "valid_object (source a)"
        "valid_arrow (source a) (target a) (morphism a)"
  using assms by (auto split:Arrow.split simp:source_def target_def)

lemma arr_id[intro]:
  assumes "valid_object s"
  shows "c.arr (Some (ID s))"
by(standard,auto simp:assms)

lemma C_someI[intro!]:
  assumes "target a = source b" "c.arr (Some a)" "c.arr (Some b)"
  shows "C (Some a) (Some b) \<noteq> None"
        "\<exists>y. C (Some a) (Some b) = Some y"
unfolding c.comp_def using assms by auto

lemma C_types:
  assumes "C (Some a) (Some b) \<noteq> None"
  shows "target a = source b"
        "source (Comp a b) = source b"
        "target (Comp a b) = target a"
using assms unfolding c.comp_def by (auto split:if_splits)

declare c.unit_Some_Id[intro] c.ide_char[simp]

lemma unit_dest[dest]:
  assumes "c.unit a"
  shows "C a (arr s t m) \<noteq> None \<Longrightarrow> Some (ID s) = a" (is "?lc \<Longrightarrow> ?l")
    and "C (arr s t m) a \<noteq> None \<Longrightarrow> Some (ID t) = a" (is "?rc \<Longrightarrow> ?r")
    and "c.arr a \<Longrightarrow> map_option source a = map_option target a"
proof -
  let ?t = "Some (ID (source (the a)))"
  from assms[unfolded c.unit_def c.null_char,rule_format,of ?t]
  have cmp:"C ?t a \<noteq> None \<Longrightarrow> C ?t a = ?t" by auto
  { assume arr:"c.arr a"
    then obtain a' where a:"a = Some a'" by auto
    have nonone:"C ?t a \<noteq> None" using a arr arr_dest(1)[THEN Arr_dest(2),THEN arr_id,OF arr] by auto
    have i1:"C ?t a = ?t" apply(rule cmp) using nonone by auto
    have "C ?t a = a" using nonone by (auto simp:c.comp_char)
    from i1[unfolded this]
    show "map_option source a = map_option target a" unfolding a
      by (cases a';auto split:Arrow.split)} note dc=this
  {assume lc:?lc hence id:"c.unit (Some (ID s))" by (auto simp:c.comp_def split:if_splits)
  from lc have "c.arr a" by (auto simp:c.comp_def split:if_splits)
  from lc dc[OF this] have "C (Some (ID s)) a \<noteq> None" by (auto simp:c.comp_def split:if_splits)
  with id[unfolded c.unit_def c.null_char,rule_format,of "a"]
       assms[unfolded c.unit_def c.null_char,rule_format,of "Some (ID s)"]
  show ?l by argo}
  assume lc:?rc hence id:"c.unit (Some (ID t))" by (auto simp:c.comp_def split:if_splits)
  from lc have "c.arr a" by (auto simp:c.comp_def split:if_splits)
  from lc dc[OF this] have "C a (Some (ID t)) \<noteq> None" by (auto simp:c.comp_def split:if_splits)
  with id[unfolded c.unit_def c.null_char,rule_format,of "a"]
       assms[unfolded c.unit_def c.null_char,rule_format,of "Some (ID t)"]
  show ?r by argo
qed

lemma dom_cod_simps[simp]:
  assumes "valid_object s" "valid_object t" "valid_arrow s t m"
  shows "c.dom (arr s t m) = (Some (ID s))" "c.cod (Some (Arrow s t m)) = (Some (ID t))"
proof -
  have h:"c.has_dom (arr s t m)" "c.has_cod (arr s t m)" using assms by auto
  have "(SOME a. c.unit a \<and> C a (Some (Arrow s t m)) \<noteq> c.null) = Some (ID s)"
    by (intro some_equality) (auto simp:assms c.null_char)
  thus "c.dom (arr s t m) = Some (ID s)" unfolding c.dom_def c.cod_def using h by auto
  have "(SOME b. c.unit b \<and> C (Some (Arrow s t m)) b \<noteq> c.null) = Some (ID t)"
    by (intro some_equality) (auto simp:assms c.null_char)
  thus "c.cod (Some (Arrow s t m)) = (Some (ID t))" unfolding c.dom_def c.cod_def using h by auto
qed

lemma isoI[intro]:
  assumes "valid_object s" "valid_object t" "valid_arrow s t m1" "valid_arrow t s m2"
          "cmp s t s m1 m2 = identity s" "cmp t s t m2 m1 = identity t"
  shows "c.iso (arr s t m1)"
proof
  have ide:"c.ide (C (arr s t m1) (arr t s m2))" "c.ide (C (arr t s m2) (arr s t m1))"
    by(auto simp: c.comp_def assms split:Arrow.split)
  show "c.inverse_arrows (arr s t m1) (arr t s m2)"
    apply(rule c.inverse_arrowsI[OF _ ide]) using assms by auto
qed

lemma iso_obj_I[intro]:
  assumes "c.iso (arr s t m1)"
  shows "iso s t" unfolding iso_def using assms by auto

end

end