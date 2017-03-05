theory MissingCategory
imports
  Limit
  Congruence
begin

section {* MissingCategory: Category theory preliminaries *}

text {*
  MissingCategory is a wrapper for the Category3 AFP entry.
  Its aim is to make the Category locale easier to use.
  First, we provide the locale ArrowCategory that will make it even easier to create instances.
  Second, this is where we keep our own generic theorems about categories.
  
  Central to our approach is to fix a datatype for morphisms in our category.
  We provide a generic implementations what all categories share:
    We find the domain and codomain of an arrow.
    The equivalence of two objects determines whether two arrows are composable.

  Those familiar with the Category3 AFP entry, it might be 
  The ArrowCategory locale follows the intuition behind the classical_category.

*}
datatype ('o,'m) Arrow = Arrow (source: 'o) (target: 'o) (morphism: 'm)
find_theorems name:Arrow name:split

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
abbreviation Id :: "'o \<Rightarrow> ('o,'m) Arrow" where "Id a \<equiv> Arrow a a (identity a)"
abbreviation Comp :: "('o,'m) Arrow \<Rightarrow> ('o,'m) Arrow \<Rightarrow> ('o,'m) Arrow" where
"Comp y x \<equiv> Arrow (source x) (target y) (cmp (source x) (target x) (target y) (morphism x) (morphism y))"

interpretation classical_category : classical_category valid_object Arr source target Id Comp
  using identity_valid cmp_valid cmp_associative identity_left identity_right
  by (unfold_locales,auto split:Arrow.split_asm)

end

end