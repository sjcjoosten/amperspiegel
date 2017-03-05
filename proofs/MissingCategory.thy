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
  assumes cmp_associative:
    "valid_arrow a b x \<Longrightarrow> valid_arrow b c y  \<Longrightarrow> valid_arrow c d z \<Longrightarrow>
     cmp a b d x (cmp b c d y z) = cmp a c d (cmp a b c x y) z"
  and cmp_valid:
     "valid_arrow a b x \<Longrightarrow> valid_arrow b c y \<Longrightarrow> valid_arrow a c (cmp a b c x y)"
  and identity_valid:
     "valid_object a \<Longrightarrow> valid_arrow a a (identity a)"
  and identity_left:
     "valid a b f \<Longrightarrow> cmp a a b (identity a) f = f"
  and identity_right:
     "valid a b f \<Longrightarrow> cmp a b b f (identity b) = f"
begin

abbreviation Arr :: "('o,'m) Arrow \<Rightarrow> bool" where
"Arr a \<equiv> (case a of Arrow s t m \<Rightarrow> valid_object s \<and> valid_object t \<and> valid_arrow s t m)"
abbreviation ID :: "'o \<Rightarrow> ('o,'m) Arrow" where "ID a \<equiv> Arrow a a (identity a)"
abbreviation Comp :: "('o,'m) Arrow \<Rightarrow> ('o,'m) Arrow \<Rightarrow> ('o,'m) Arrow" where
"Comp y x \<equiv> Arrow (source x) (target y) (cmp (source x) (target x) (target y) (morphism x) (morphism y))"

sublocale c : classical_category valid_object Arr source target ID Comp
  using identity_valid cmp_valid cmp_associative identity_left identity_right
  by (unfold_locales,auto split:Arrow.split_asm)
sublocale op : classical_category valid_object Arr target source ID "\<lambda> y x. Comp x y"
  using identity_valid cmp_valid cmp_associative identity_left identity_right
  by (unfold_locales,auto split:Arrow.split_asm)
sublocale op_c: category op.comp using op.category_axioms.
sublocale c_c: category c.comp using c.category_axioms.

abbreviation "C x y \<equiv> c.comp x y"
lemma op_is_op : "C y x = op.comp x y" by (auto simp: "c.comp_def" "op.comp_def")
lemmas cat_simps[simp] = c.null_char
lemmas cat_intros[intro] = c.category_axioms c.partial_magma_axioms

end

end