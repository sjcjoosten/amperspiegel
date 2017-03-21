theory MissingCategory
imports
  Limit
begin

section {* MissingCategory: Category theory preliminaries *}

text {*
  MissingCategory is a wrapper for the Category3 AFP entry.
  Its aim is to make the Category locale easier to use.
  First, we provide the locale arrow_category that will make it even easier to create instances.
  Second, this is where we keep our own generic theorems about categories.

  To make it easier to create instances, we fix a datatype for morphisms in the category.
  This provides generic implementations for what all categories share:
    Finding domain and codomain of an arrow correctly.
    Determining whether two arrows are composable through domain and codomain.
  In addition, we implement our own preference to work with (compose f g) = g \<circ> f

  One of the generic facts about categories, is that every category has an opposite.
  arrow_category instantiates both: that of the category and its opposite.

  Those familiar with the Category3 AFP entry, it might be 
  The arrow_category locale follows the intuition behind the classical_category.

*}
datatype ('o,'m) Arrow = Arrow (source: 'o) (target: 'o) (morphism: 'm)
datatype ('o,'m) Category
 = Category (valid_arrow : "'o \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> bool")
            (valid_object: "'o \<Rightarrow> bool")
            (composition : "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm")
            (cat_identity: "'o \<Rightarrow> 'm")

abbreviation "op_a x \<equiv> Arrow (target x) (source x) (morphism x)"
definition op_arr where "op_arr \<equiv> map_option op_a"
lemma op_arr_None[simp]:"op_arr None = None" "op_arr x = None \<longleftrightarrow> x = None"
  unfolding op_arr_def by auto
lemma source_target_Some_op_arr[simp]:
  shows
  "source   (the (op_arr (Some x))) = target   x"
  "target   (the (op_arr (Some x))) = source   x"
  "morphism (the (op_arr (Some x))) = morphism x"
by (auto simp:op_arr_def)
lemma source_target_the_op_arr[simp]:
  assumes "x \<noteq> None" shows
  "source   (the (op_arr x)) = target   (the x)"
  "target   (the (op_arr x)) = source   (the x)"
  "morphism (the (op_arr x)) = morphism (the x)"
using assms by auto
lemma source_target_op_arr[simp]:
  "map_option source (op_arr x) = map_option target x"
  "map_option target (op_arr x) = map_option source x"
  "map_option morphism (op_arr x) = map_option morphism x"
by (cases x,auto simp:op_arr_def)+
lemma op_arr_congr[simp]:
  "op_arr x = op_arr y \<longleftrightarrow> x = y" by (cases x;cases y,auto simp:op_arr_def Arrow.expand)

locale CatNotation =
  fixes Cat::"('o,'m) Category"
begin
  abbreviation "va  \<equiv> valid_arrow  Cat"
  abbreviation "vo  \<equiv> valid_object Cat"
  abbreviation "cmp \<equiv> composition  Cat"
  abbreviation "idt \<equiv> cat_identity     Cat"
end

context classical_category begin
  lemma arr_None[dest]:"arr None \<Longrightarrow> False" by (auto simp:arr_char)
  definition "lift f \<equiv> case_option None (\<lambda> a. if Arr a then Some (f a) else None)"
  abbreviation "fix \<equiv> lift id"
  lemma lift_compose:
    assumes "\<And> a. Arr a \<Longrightarrow> Arr (g a)"
    shows "lift f (lift g x) = lift (f o g) x" using assms by (cases x;auto simp:o_def lift_def)
  lemma lift_some[simp]:
    shows "lift f (Some x) = Some (f x) \<longleftrightarrow> Arr x" by (auto simp: lift_def split:if_splits)
  lemma lift_none[simp]:
    shows "lift f None = None" 
          "lift f (Some x) = None \<longleftrightarrow> \<not> Arr x" by (auto simp: lift_def split:if_splits )
  lemma lift_noneI[intro]:
    assumes "\<not> arr x"
    shows "lift f x = None" using assms by (cases x,auto simp:arr_char)
  lemma fix2[simp]:"fix (fix a) = fix a" using lift_compose[of id]
    by (cases a;auto)
  lemma fix_iff[simp]:shows "fix (Some a) = (Some a) \<longleftrightarrow> Arr a"
    using lift_some[of id] by (auto)
  lemma fix_None[simp]: "fix None = None" by auto
  lemma fix_NoneI[intro]: "\<not> Arr aa \<Longrightarrow> fix (Some aa) = None" by auto

  lemma fix_char:shows "fix a = (if arr a then a else None)"
     by (cases a,auto simp:arr_char)
  lemma fix_None_iff[simp]: "fix x = None \<longleftrightarrow> \<not> arr x" 
     by(cases x,auto simp:arr_char)
  lemma fix_congr2: assumes "arr a"
     shows "fix a = fix b \<longleftrightarrow> a = b" using assms by (cases b,auto simp:fix_char)
  lemma fix_congr: assumes "arr b"
     shows "fix a = fix b \<longleftrightarrow> a = b" using assms by (cases a,auto simp:fix_char)
  lemma arr_fix[simp]: "arr (fix x) \<longleftrightarrow> arr x" by (auto simp:fix_char)
  lemma domcod_fix[simp]:
    "fix (dom x) = dom x" "fix (cod x) = cod x"
    "dom (fix x) = dom x" "cod (fix x) = cod x"
    using Obj_Dom[of "the x"] Obj_Cod[of "the x"]
    by (auto simp:dom_char cod_char fix_char arr_char)
  lemma fix_to_lift[simp]:
    "map_option f o fix = lift f" "map_option f (fix x) = lift f x"
    by (standard,auto simp:lift_def split:option.split)

  lemma comp_None[simp]:
    "comp x None = None"
    "comp None x = None"
  by (auto simp:comp_char)

  lemma comp_NoneI:
    assumes "\<not> arr x \<or> \<not> arr y \<or> cod y \<noteq> dom x"
    shows "comp x y = None" "None = comp x y"
  using assms by (auto simp:comp_char arr_char cod_char dom_char)

  lemma dom_cod_None[simp]:
    shows "dom None = None" "cod None = None"
  by (auto simp:dom_def has_dom_def cod_def has_cod_def null_char)

  lemma comp_fix[simp]:
    "comp (fix x) y = comp x y"
    "comp x (fix y) = comp x y"
    "fix (comp x y) = comp x y" by (auto simp:fix_char intro:comp_NoneI)
end

locale arrow_category = CatNotation Cat 
  for Cat::"('o,'m) Category" +
  assumes cmp_associative[simp]:
    "va a b x \<Longrightarrow> va b c y  \<Longrightarrow> va c d z \<Longrightarrow>
     cmp a b d x (cmp b c d y z) = cmp a c d (cmp a b c x y) z"
  and cmp_valid[intro]:
     "va a b x \<Longrightarrow> va b c y \<Longrightarrow> va a c (cmp a b c x y)"
  and identity_valid[intro]:
     "vo a \<Longrightarrow> va a a (idt a)"
  and identity_left[simp]:
     "va a b f \<Longrightarrow> cmp a a b (idt a) f = f"
  and identity_right[simp]:
     "va a b f \<Longrightarrow> cmp a b b f (idt b) = f"
begin
  
  lemma identity_cmp[simp]:
     assumes "vo X"
     shows "cmp X X X (idt X) (idt X) = idt X"
  using identity_left[OF identity_valid[OF assms]].

  definition Arr :: "('o,'m) Arrow \<Rightarrow> bool" where
  "Arr a \<equiv> (case a of Arrow s t m \<Rightarrow> vo s \<and> vo t \<and> va s t m)"
  abbreviation ID :: "'o \<Rightarrow> ('o,'m) Arrow" where "ID a \<equiv> Arrow a a (idt a)"
  definition Comp :: "('o,'m) Arrow \<Rightarrow> ('o,'m) Arrow \<Rightarrow> ('o,'m) Arrow" where
  "Comp y x \<equiv> Arrow (source x) (target y) (cmp (source x) (target x) (target y) (morphism x) (morphism y))"
  
  sublocale c : classical_category vo Arr source target ID Comp
    by (unfold_locales,auto split:Arrow.split_asm simp:Comp_def Arr_def)
  
  abbreviation "C x y \<equiv> c.comp y x"
  notation C (infix ";" 3)

  abbreviation "arr s t m \<equiv> Some (Arrow s t m)"
  
  definition iso where "iso s t \<equiv> (\<exists> m. c.iso (arr s t m))"
  
  declare c.null_char[simp]
  lemma semi_opposite_category[intro]:
    "arrow_category (Category (\<lambda> x y. va y x) vo (\<lambda> a b c s t. cmp c b a t s) idt)"
    by standard auto
  interpretation dc : dual_category c.comp
    by unfold_locales
  declare dc.comp_char[simp del]
  declare dc.is_category[intro]
  lemma dual_comp[simp]:"dc.comp x y = (c.comp y x)" unfolding dc.comp_char by auto
  lemma dual_ide[simp]:"dc.ide x = c.ide x" by auto
  lemma dual_null[simp]:"dc.null = None" by auto
  lemma dual_dom[simp]:"dc.dom x = c.cod x" by auto
  lemma dual_cod[simp]:"dc.cod x = c.dom x" by auto
  lemma dual_arr[simp]:"dc.arr x = c.arr x" by auto
  lemma dual_hom[simp]:"dc.hom x y = c.hom y x" by auto
  lemma dual_par[simp]:"dc.par x y = c.par x y" by auto

  lemma category_op[intro]:"category_axioms op ;" "partial_magma op ;"
    using dc.is_category[unfolded category_def dual_comp]
    by auto

  lemma Arr[simp]:
    shows "Arr a \<longleftrightarrow> (vo (target a) \<and> vo (source a) \<and> va (source a) (target a) (morphism a))"
    by (auto split:Arrow.split simp:source_def target_def Arr_def)

  lemma has_dom_cod_arrI[intro]:
    assumes "vo (source a)" "vo (target a)"
            "va (source a) (target a) (morphism a)"
    shows "c.has_dom (Some a)"
          "c.has_cod (Some a)"
          "c.arr (Some a)"
  proof -
    obtain s t m where a[simp]:"a = Arrow s t m" by (cases a)
    have h:"C (Some (Arrow s t m)) (Some (ID t)) \<noteq> None"
           "C (Some (ID s)) (Some (Arrow s t m)) \<noteq> None"
      unfolding c.comp_def using assms by auto
    show "c.has_dom (Some a)" unfolding c.has_dom_def using h
      by auto (auto intro:c.unit_Some_Id[OF assms(1)])
    show "c.has_cod (Some a)" unfolding c.has_cod_def using h
      by auto (auto intro:c.unit_Some_Id[OF assms(2)])
    thus "c.arr (Some a)" unfolding c.arr_def by blast
  qed
  
  lemma arr_dest[simp]:
    shows "c.arr a \<longleftrightarrow> Arr (the a) \<and> a = (Some (the a))"
    unfolding c.arr_char by auto
  
  lemma arr_I[intro]:
    assumes "Arr (the a)" "a \<noteq> None"
    shows "c.arr a"
    using assms unfolding c.arr_char by auto
  
  lemma arr_id:
    assumes "vo s"
    shows "c.arr (Some (ID s))"
  by(standard,auto intro:assms)

  lemma arr_Arrow[intro]:
    assumes "vo (source x)" "vo (target x)" "va (source x) (target x) (morphism x)"
    shows "c.arr (Some x)"
  by(standard,auto intro:assms)
  
  lemma C_someI[intro]:
    assumes "target a = source b" "c.arr (Some a)" "c.arr (Some b)"
    shows "C (Some a) (Some b) \<noteq> None"
          "\<exists>y. C (Some a) (Some b) = Some y"
  unfolding c.comp_def using assms by auto

  lemma va_cmpI[intro]:
    assumes "Arr a" "Arr b" "target a = source b"
    shows "va (source a) (target b) (cmp (source a) (source b) (target b) (morphism a) (morphism b))"
  using assms by auto
  
  lemma C_types:
    assumes "C (Some a) (Some b) \<noteq> None"
    shows "target a = source b"
          "source (Comp a b) = source b"
          "target (Comp a b) = target a"
  using assms unfolding c.comp_def by (auto split:if_splits simp:Comp_def)
  
  declare c.unit_Some_Id[intro] c.comp_char[simp]
  
  lemma unit_dest[dest]:
    assumes "c.unit a"
    shows "C a (arr s t m) \<noteq> None \<Longrightarrow> Some (ID s) = a" (is "?lc \<Longrightarrow> ?l")
      and "C (arr s t m) a \<noteq> None \<Longrightarrow> Some (ID t) = a" (is "?rc \<Longrightarrow> ?r")
      and "c.arr a \<Longrightarrow> map_option source a = map_option target a"
  proof -
    let ?t = "Some (ID (source (the a)))"
    note [split]=if_splits
    from assms[unfolded c.unit_def,rule_format,of ?t]
      have cmp:"C ?t a \<noteq> None \<Longrightarrow> C ?t a = ?t" by auto
    { assume arr:"c.arr a"
      then obtain a' where a:"a = Some a'" by auto
      have nonone:"C ?t a \<noteq> None" using arr by auto
      hence i1:"C ?t a = ?t" "C ?t a = a" by(intro cmp,auto)
      thus "map_option source a = map_option target a" unfolding a
        by (cases a';auto split:Arrow.split)} note dc=this
    {assume lc:?lc hence id:"c.unit (Some (ID s))" by auto
    from lc have "c.arr a" by auto
    from lc dc[OF this] have "C (Some (ID s)) a \<noteq> None" by auto
    with id[unfolded c.unit_def,rule_format,of "a"]
         assms[unfolded c.unit_def,rule_format,of "Some (ID s)"]
    show ?l by auto}
    assume lc:?rc hence id:"c.unit (Some (ID t))" by auto
    from lc have "c.arr a" by (auto split:if_splits)
    from lc dc[OF this] have "C a (Some (ID t)) \<noteq> None" by auto
    with id[unfolded c.unit_def,rule_format,of "a"]
         assms[unfolded c.unit_def,rule_format,of "Some (ID t)"]
    show ?r by auto
  qed
  
  lemma dom_cod_simps[simp]:
    assumes "vo s" "vo t" "va s t m"
    shows "c.dom (arr s t m) = (Some (ID s))" "c.cod (arr s t m) = (Some (ID t))"
  proof -
    have h:"c.has_dom (arr s t m)" "c.has_cod (arr s t m)" using assms by auto
    have "(SOME a. c.unit a \<and> C a (Some (Arrow s t m)) \<noteq> c.null) = Some (ID s)"
      by (rule some_equality,auto intro:assms split:if_splits simp:Arr_def)
    thus "c.dom (arr s t m) = Some (ID s)" unfolding c.dom_def c.cod_def using h by auto
    have "(SOME b. c.unit b \<and> C (Some (Arrow s t m)) b \<noteq> c.null) = Some (ID t)"
      by (rule some_equality,auto intro:assms split:if_splits simp:Arr_def)
    thus "c.cod (Some (Arrow s t m)) = (Some (ID t))" unfolding c.dom_def c.cod_def using h by auto
  qed
  
  lemma dom_cod_id_simps[simp]:
    assumes "vo s"
    shows "c.dom (Some (ID s)) = Some (ID s)" "c.cod (Some (ID s)) = Some (ID s)"
  using dom_cod_simps[OF assms assms identity_valid[OF assms]].

  lemma nothing_None_object[intro]:
    assumes "\<not> vo s"
    shows "c.dom (arr s t m) = None" "c.dom (arr t s m) = None"
          "c.cod (arr s t m) = None" "c.cod (arr t s m) = None"
  using assms by (auto simp:c.dom_def c.has_dom_def c.cod_def c.has_cod_def)

  lemma nothing_None_arrow[intro]:
    assumes "\<not> va s t m"
    shows "c.dom (arr s t m) = None" "c.cod (arr s t m) = None"
  using assms by (auto simp:c.dom_def c.has_dom_def c.cod_def c.has_cod_def)
  
  declare c.ide_char[simp]

  lemma isoI[intro]:
    assumes "vo s" "vo t" "va s t m1" "va t s m2"
            "cmp s t s m1 m2 = idt s" "cmp t s t m2 m1 = idt t"
    shows "c.iso (arr s t m1)"
  proof
    have ide:"c.ide (C (arr s t m1) (arr t s m2))" "c.ide (C (arr t s m2) (arr s t m1))"
      by(auto simp: assms Comp_def split:Arrow.split)
    show "c.inverse_arrows (arr s t m1) (arr t s m2)"
      by(rule c.inverse_arrowsI[OF _ ide],insert assms, auto)
  qed

  lemma ide_ID[intro]:
    assumes "vo s"
    shows "c.ide (Some (ID s))" by (standard,insert assms identity_valid,auto)

  lemma iso_obj_I[intro]:
    assumes "c.iso (arr s t m1)"
    shows "iso s t" unfolding iso_def using assms by auto

  declare c.iso_is_arr[simp del] c.ideD[simp del]

  lemma op_arr_ID[simp]:
    "op_arr (c.cod x) = c.cod x"
    "op_arr (c.dom x) = c.dom x"
    "op_arr (Some (ID a)) = Some (ID a)"
    by (auto simp:c.cod_char c.dom_char op_arr_def)

  lemma constant_functor_ax[intro]:
    assumes "vo D"
    shows "constant_functor_axioms c.comp (Some (ID D))"
  using assms by(unfold_locales,auto)

  lemma constant_functor[intro]:
    assumes "vo D" "category x"
    shows "constant_functor x c.comp (Some (ID D))"
  using assms by(intro_locales,auto simp:category_def)
  
  lemma C_unfolded[simp]:
    shows "C (Some (Arrow x1 x2 x3)) (Some (Arrow x2 x2a x3a)) =
           (if va x1 x2 x3 \<and> va x2 x2a x3a \<and> vo x1 \<and> vo x2 \<and> vo x2a then Some (Arrow x1 x2a (cmp x1 x2 x2a x3 x3a)) else None)"
    unfolding Comp_def c.comp_char by auto
  declare c.comp_char[simp del]
end

declare constant_functor.is_functor[intro]

text {*
  The arrow_functor locale introduces a Functor between ArrowCategories.
  
*}
type_synonym ('o,'m) C = "('o,'m) Arrow option \<Rightarrow> ('o,'m) Arrow option \<Rightarrow> ('o,'m) Arrow option"

locale arrow_functor =
  c1:arrow_category Cat1+
  c2:arrow_category Cat2
  for Cat1 :: "('o1, 'm1) Category"
  and Cat2 :: "('o2, 'm2) Category"
  and F_o :: "'o1 \<Rightarrow> 'o2"
  and F_m :: "'o1 \<Rightarrow> 'o1 \<Rightarrow> 'm1 \<Rightarrow> 'm2" +
  assumes validity_m[simp]:"c1.vo a \<Longrightarrow> c1.vo b \<Longrightarrow> c1.va a b m \<Longrightarrow> c2.va (F_o a) (F_o b) (F_m a b m)"
      and validity_o[simp]:"c1.vo a \<Longrightarrow> c2.vo (F_o a)"
      and validity_i[simp]:"c1.vo x1 \<Longrightarrow> c2.idt (F_o x1) = F_m x1 x1 (c1.idt x1)"
      and validity_c[simp]:"c1.vo a \<Longrightarrow> c1.vo b \<Longrightarrow> c1.vo c \<Longrightarrow> c1.va a b m1 \<Longrightarrow> c1.va b c m2
          \<Longrightarrow> c2.cmp (F_o a) (F_o b) (F_o c) (F_m a b m1) (F_m b c m2) = F_m a c (c1.cmp a b c m1 m2)"
begin
  fun Functor where 
    "Functor None = None" |
    "Functor (Some (Arrow s t m))
      = (if c1.Arr (Arrow s t m) then Some (Arrow (F_o s) (F_o t) (F_m s t m)) else None)"

  lemma functor_none[simp]: "(Functor x = None) \<longleftrightarrow> \<not> (c1.c.arr x)"
    by (cases x;cases "the x";auto)

  lemma "functor_ax"[intro]: "functor_axioms c1.c.comp c2.c.comp Functor"
  proof -
    note [simp] = c1.c.dom_char c1.c.cod_char c1.nothing_None_arrow c1.nothing_None_object c1.Arr_def
    show "functor_axioms c1.c.comp c2.c.comp Functor"
    proof(standard,goal_cases)
      case (1 f) thus ?case by (cases f;cases "the f",auto) next
      case (2 f) thus ?case by (cases f;cases "the f",auto) next
      case (3 f) thus ?case by (cases f;cases "the f") auto next
      case (4 f) thus ?case by (cases f;cases "the f") auto next
      case (5 f g) thus ?case by (cases g;cases "the f";cases "the g")
                                 (auto simp:)
  qed qed

  lemma "functor"[intro]: "functor c1.c.comp c2.c.comp Functor" by intro_locales auto
  sublocale "functor":"functor" c1.c.comp c2.c.comp Functor by standard
  sublocale diagram:diagram c1.c.comp c2.c.comp Functor by standard
  
  lemma "functor_map"[intro]:
    assumes "c2.vo D"
    shows "functor c1.c.comp c2.c.comp (constant_functor.map c1.c.comp c2.c.comp (Some (c2.ID D)))"
  using constant_functor.is_functor[OF c2.constant_functor[OF assms c1.c.category_axioms]].

  lemma "functor_map_ax"[intro]:
    assumes "c2.vo D"
    shows "functor_axioms c1.c.comp c2.c.comp (constant_functor.map c1.c.comp c2.c.comp (Some (c2.ID D)))"
  using functor_map[OF assms,unfolded functor_def] by auto

end  

fun Dual where
  "Dual (Category va vo cmp idt)
    = (Category (\<lambda> a b m. va b a m) vo (\<lambda> a b c x y. cmp c b a y x) idt)"

lemma op_op[simp]:
  "(op_arr (op_arr y)) = y" by (cases y;auto simp:op_arr_def)

locale arrow_category_with_dual = arrow_category Cat for Cat
begin
  abbreviation "dual \<equiv> Dual Cat"
  lemma Dual_simps[simp]:
    "valid_arrow dual a b x = va b a x"
    "composition dual a b c x y = cmp c b a y x"
    "valid_object dual a = vo a"
    "cat_identity dual a = idt a"
    by(cases Cat,auto)+
  sublocale dual : arrow_category dual by standard auto
  lemma dual_c_link[simp]:
    "op_arr (dual.c.comp x y) = c.comp (op_arr y) (op_arr x)"
    "dual.vo = vo"
    by (auto simp:op_arr_def c.comp_char dual.c.comp_char Comp_def dual.Comp_def Arr_def
             split:Arrow.split)
  lemma dual_ID[simp]:"dual.ID x = ID x" by auto
  lemma dual_Arr[simp]:"dual.Arr x = Arr (op_a x)" by (auto simp: Arr_def)
  lemma dual_arr2[simp]:"dual.c.arr x = c.arr (op_arr x)"
    unfolding dual.c.arr_char c.arr_char op_arr_def by (auto split:Arrow.split simp:op_arr_def)
  lemma dual_dom2[simp]:"dual.c.dom x = c.cod (op_arr x)"
    unfolding dual.c.dom_char c.cod_char dual_arr2 dual_ID by (cases x,auto)
  lemma dual_cod2[simp]:"dual.c.cod x = c.dom (op_arr x)"
    unfolding dual.c.cod_char c.dom_char dual_arr2 dual_ID by (cases x,auto)
  lemma dual_par2[simp]:"dual.c.par f f' = c.par (op_arr f) (op_arr f')"
    unfolding dual_dom2 dual_cod2 dual_arr2 by auto
  lemma dual_comp2[simp]:"dual.c.comp y x = op_arr (c.comp (op_arr x) (op_arr y))"
    unfolding dual.c.comp_char c.comp_char by (auto simp:op_arr_def Comp_def dual.Comp_def)
  lemma dual_hom2[simp]:"dual.c.hom x y = op_arr ` c.hom y x"
    unfolding set_eq_iff
    proof(standard,goal_cases)
      case (1 f) 
      hence "f \<in> dual.c.hom x y \<longleftrightarrow> op_arr f \<in> c.hom y x"
        unfolding dual_arr2 dual_cod2 dual_dom2 by auto
      also have "\<dots> \<longleftrightarrow> f \<in> op_arr ` c.hom y x"
        using imageI[of "op_arr f" _ "op_arr"] by fastforce
      finally show ?case.
    qed
  lemma dual_fix:"op_arr o dual.c.fix = c.fix o op_arr"
    proof(standard,goal_cases) case (1 x)
      thus ?case by(cases x,auto simp:op_arr_def c.lift_def dual.c.lift_def split:Arrow.split)
    qed
  lemma op_arr_char1:"op_arr o c.fix = c.lift op_a"
    unfolding op_arr_def by auto
  lemma op_arr_char2:"c.fix o op_arr = dual.c.lift op_a"
    unfolding dual_fix[symmetric] unfolding op_arr_def by auto
  
  (* TODO: use arrow_functor instead ! *)
  lemma dual_arrow_functor_axioms[intro]: "functor_axioms dual.c.comp op ; (c.fix \<circ> op_arr)"
    apply(subst dual_comp[symmetric])
    proof(unfold_locales,goal_cases)
      case (1 f)
      then show ?case unfolding dual_arr2 by auto
    next
      case (2 f)
      then show ?case unfolding dual_arr2 c.fix_char by auto
    next
      case (3 f)
      show ?case by auto
    next
      case (4 f)
      show ?case by auto
    next
      case (5 f g)
      show ?case unfolding o_def dual_comp2 c.comp_fix dual_comp op_op using refl.
    qed

  lemma dual_arrow_functor[intro]: "functor dual.c.comp op ; (c.fix \<circ> op_arr)"
    by intro_locales standard+

  lemma ff_functor[intro]:"faithful_functor_axioms dual.c.comp (c.fix \<circ> op_arr) "
    proof(unfold_locales,goal_cases)
      case (1 f f') hence ca:"c.arr (op_arr f')" unfolding dual_par2 by auto
      from 1(2) show ?case unfolding o_def c.fix_congr[OF ca] by auto
    qed
  
  interpretation ff_functor:"faithful_functor" dual.c.comp C "c.fix o op_arr"
    by intro_locales standard+
  (* TODO: develop this into two natural isomorphisms *)
  (* Prove this after fixing the proof above with arrow_functor :
  interpretation ff_functor:"faithful_functor" C dual.c.comp "c.lift op_arr"
    by intro_locales standard+
    (Not urgent: I really only need functor composition with op_arr in one direction)
  *)
  term natural_transformation
  term natural_isomorphism
end


abbreviation "span_va \<equiv> \<lambda> a b (). a = finite_3.a\<^sub>1 \<or> a = b"
abbreviation "const_T \<equiv> \<lambda> _ . True"
abbreviation "comp_unit \<equiv> \<lambda> _ _ _ () () . ()"
abbreviation "const_unit \<equiv> \<lambda> _ . ()"
definition   "span \<equiv> (Category span_va const_T comp_unit const_unit)"

interpretation span : (* the canonical span and cospan *)
  arrow_category_with_dual span by standard (auto simp:span_def Nitpick.case_unit_unfold)

lemma span_invalids[dest]:
  "span.va finite_3.a\<^sub>2 finite_3.a\<^sub>1 () \<Longrightarrow> False"
  "span.va finite_3.a\<^sub>3 finite_3.a\<^sub>1 () \<Longrightarrow> False"
  "span.va finite_3.a\<^sub>2 finite_3.a\<^sub>3 () \<Longrightarrow> False"
  "span.va finite_3.a\<^sub>3 finite_3.a\<^sub>2 () \<Longrightarrow> False"
  by (auto simp:span_def)

lemma span_valids[intro]:
  "span.va finite_3.a\<^sub>1 finite_3.a\<^sub>1 ()"
  "span.va finite_3.a\<^sub>1 finite_3.a\<^sub>2 ()"
  "span.va finite_3.a\<^sub>1 finite_3.a\<^sub>3 ()"
  "span.va finite_3.a\<^sub>2 finite_3.a\<^sub>2 ()"
  "span.va finite_3.a\<^sub>3 finite_3.a\<^sub>3 ()"
  by (auto simp:span_def)

lemma span_object[intro]:
  "span.vo x" by (auto simp:span_def)

lemma cospan_invalids[dest]:
  "span.dual.va finite_3.a\<^sub>1 finite_3.a\<^sub>2 () \<Longrightarrow> False"
  "span.dual.va finite_3.a\<^sub>1 finite_3.a\<^sub>3 () \<Longrightarrow> False"
  "span.dual.va finite_3.a\<^sub>3 finite_3.a\<^sub>2 () \<Longrightarrow> False"
  "span.dual.va finite_3.a\<^sub>2 finite_3.a\<^sub>3 () \<Longrightarrow> False"
  by (auto simp:span_def)

lemma cospan_valids[intro]:
  "span.dual.va finite_3.a\<^sub>1 finite_3.a\<^sub>1 ()"
  "span.dual.va finite_3.a\<^sub>2 finite_3.a\<^sub>1 ()"
  "span.dual.va finite_3.a\<^sub>3 finite_3.a\<^sub>1 ()"
  "span.dual.va finite_3.a\<^sub>2 finite_3.a\<^sub>2 ()"
  "span.dual.va finite_3.a\<^sub>3 finite_3.a\<^sub>3 ()"
  by (auto simp:span_def)

lemma cospan_object[intro]:
  "span.dual.vo x" by (auto simp:span_def)

lemma span_dom_cod[simp]:
  assumes "span.va x y ()"
  shows "span.c.dom (Some (Arrow x y ())) = Some (Arrow x x ())"
        "span.c.cod (Some (Arrow x y ())) = Some (Arrow y y ())"
  using span.dom_cod_simps[OF span_object span_object assms] by auto

locale span_diagram =
  category C +
  diagram span.c.comp C F
  for C :: "'b comp"
  and F :: "(Enum.finite_3, unit) Arrow option \<Rightarrow> 'b"

locale cospan_diagram =
  category C +
  diagram span.dual.c.comp C F
  for C :: "'b comp"
  and F :: "(Enum.finite_3, unit) Arrow option \<Rightarrow> 'b"

context arrow_category begin
(* span_of creates a functor belonging to a span_diagram X <-f- Z -g-> Y. *)
fun span_of_obj where
  "span_of_obj X Y Z finite_3.a\<^sub>1 = Z" |
  "span_of_obj X Y Z finite_3.a\<^sub>2 = X" |
  "span_of_obj X Y Z finite_3.a\<^sub>3 = Y"
fun span_of_m where
  "span_of_m X Y Z f g finite_3.a\<^sub>1 finite_3.a\<^sub>2 () = f" |
  "span_of_m X Y Z f g finite_3.a\<^sub>1 finite_3.a\<^sub>3 () = g" |
  "span_of_m X Y Z f g i _ () = idt (span_of_obj X Y Z i)"

lemma span_of_is_functor[intro]:
  assumes "va Z X f" "va Z Y g" "vo X" "vo Y" "vo Z" 
  shows "arrow_functor span Cat (span_of_obj X Y Z) (span_of_m X Y Z f g)"
proof(unfold_locales,goal_cases)
  case (1 a b m) thus ?case using assms by(cases a;cases b,auto)
next
  case (2 a) thus ?case using assms by(cases a,auto)
next
  case (3 x1) thus ?case using assms by(cases x1,auto)
next
  case (4 a b c m1 m2) thus ?case using assms by(cases a;cases b;cases c,auto)
qed

abbreviation cospan_of_m where
  "cospan_of_m X Y Z f g s t m \<equiv> span_of_m X Y Z f g t s m"

lemma cospan_of_is_functor[intro]:
  assumes "va X Z f" "va Y Z g" "vo X" "vo Y" "vo Z" 
  shows "arrow_functor span.dual Cat (span_of_obj X Y Z) (cospan_of_m X Y Z f g)"
proof(unfold_locales,goal_cases)
  case (1 a b m) thus ?case using assms by(cases a;cases b,auto)
next
  case (2 a) thus ?case using assms by(cases a,auto)
next
  case (3 x1) thus ?case using assms by(cases x1,auto)
next
  case (4 a b c m1 m2) thus ?case using assms by(cases a;cases b;cases c,auto)
qed

end

(*    A pullback for a cospan X -f-> Z <-g- Y consists of a
   span X <-h- D -k-> Y such that fh = gk and such that
   if X <-h'- D' -k'-> Y is any span such that fh' = gk',
   then there exists a unique l: D' --> D
   such that h' = hl and k' = kl.
 *)
term cone
locale pullback =
  L: limit_cone span.dual.c.comp C F a \<chi>
for C F a \<chi>

(*
  locale pullback_cone =
    J: cospan +
    C: category C +
    D: cospan_diagram C f g +
    limit_cone J.comp C D.map "C.dom h" "D.mkCone h k"
  for C :: "'c comp"
  and f :: 'c
  and g :: 'c
  and h :: 'c
  and k :: 'c
*)
find_consts name:cones_map

(*
  valid_obj and valid_arr require that:

  D —k\<longrightarrow> Y
  |       |
  h       g
  \<down>       \<down>
  X —f\<longrightarrow>Z

  is_cone requires that the diagram above commutes.
  It is a pullback because it is also universal:
    any D' h' k' forming a diagram like the above will have a unique arrow u from D' to D.
*)
locale arrow_pullback =
  C: arrow_category Cat
  for Cat :: "('o, 'm) Category" and X Y Z D f g h k +
  assumes valid_obj[intro]:"C.vo X" "C.vo Y" "C.vo Z" "C.vo D"
  and valid_arr[intro]: "C.va X Z f" "C.va Y Z g" "C.va D X h" "C.va D Y k"
  and is_cone:"C.cmp D X Z h f = C.cmp D Y Z k g"
  and is_universal: "C.cmp D' X Z h' f = C.cmp D' Y Z k' g \<and> C.vo D' \<and> C.va D' X h' \<and> C.va D' Y k'
                 \<Longrightarrow> \<exists>!u. C.va D' D u \<and> C.cmp D' D X u h = h' \<and> C.cmp D' D Y u k = k'"
begin
  abbreviation "diagonal \<equiv> C.cmp D Y Z k g"
  sublocale co: arrow_functor span.dual Cat "C.span_of_obj X Y Z" "C.cospan_of_m X Y Z f g"
    by auto
  interpretation sp: arrow_functor span Cat "C.span_of_obj X Y D" "C.span_of_m X Y D h k"
    by auto
  interpretation cf:constant_functor span.dual.c.comp C.c.comp "Some (C.ID D)"
    using span.dual.c.category_axioms by auto
  fun \<chi> :: "(Enum.finite_3, unit) Arrow option \<Rightarrow> ('o, 'm) Arrow option"  where
  "\<chi> (Some (Arrow _ finite_3.a\<^sub>1 ())) = Some (Arrow D Z diagonal)" |
  "\<chi> (Some (Arrow finite_3.a\<^sub>2 finite_3.a\<^sub>2 ())) = Some (Arrow D X h)" |
  "\<chi> (Some (Arrow finite_3.a\<^sub>3 finite_3.a\<^sub>3 ())) = Some (Arrow D Y k)" |
  "\<chi> _ = None"
  lemma dom_cod_Z[simp]:
    "C.c.dom (Some (Arrow D Z diagonal)) = Some (C.ID D)"
    "C.c.cod (Some (Arrow D Z diagonal)) = Some (C.ID Z)"
    "C.c.cod (Some (Arrow D X h)) = Some (C.ID X)"
    "C.c.cod (Some (Arrow D Y k)) = Some (C.ID Y)"
  using C.dom_cod_simps[OF valid_obj(4,3) C.cmp_valid[OF valid_arr(3,1),unfolded is_cone]]
        C.dom_cod_simps[OF valid_obj(4,2) valid_arr(4)]
        C.dom_cod_simps[OF valid_obj(4,1) valid_arr(3)]
        by auto

  interpretation cone: cone span.dual.c.comp C.c.comp co.Functor "Some (C.ID D)" \<chi>
  proof(standard,goal_cases)
    case (1 f)
    then show ?case by (cases f;cases "the f";cases "source (the f)";cases "target (the f)",auto)
  next
    case (2 f)
    with valid_obj valid_arr show ?case
      by (cases "the f";cases "source (the f)";cases "target (the f)",
          auto simp: op_arr_def cf.map_def)
  next
    case (3 f)
    then show ?case
      by (cases "the f";cases "source (the f)";cases "target (the f)",
          auto simp: op_arr_def cf.map_def)
  next
    case (4 f)
    then show ?case
      by (cases "the f";cases "source (the f)";cases "target (the f)")
         (auto simp:op_arr_def C.Comp_def is_cone)
  next
    case (5 f)
    then show ?case
      by (cases "the f";cases "source (the f)";cases "target (the f)")
         (auto simp:op_arr_def C.Comp_def is_cone)
  qed

  sublocale pullback : pullback C.c.comp co.Functor "Some (C.ID D)" \<chi>
  proof(intro_locales,standard,goal_cases)
    case (1 a' \<chi>')
    let ?cf = "constant_functor.map span.dual.c.comp C.c.comp a'"
    have cf:"constant_functor_axioms C.c.comp a'" "constant_functor span.dual.c.comp C.c.comp a'"
     and nt:"\<And> f. span.dual.c.arr f \<Longrightarrow> C.c.dom (\<chi>' f) = constant_functor.map span.dual.c.comp C.c.comp a' (span.dual.c.dom f)"
            "\<And> f. span.dual.c.arr f \<Longrightarrow> C.c.cod (\<chi>' f) = co.Functor (span.dual.c.cod f)"
            "\<And> f. span.dual.c.arr f \<Longrightarrow> C.C (\<chi>' (span.dual.c.dom f)) (co.Functor f) = \<chi>' f"
            "\<And> f. span.dual.c.arr f \<Longrightarrow> C.C (constant_functor.map span.dual.c.comp C.c.comp a' f) (\<chi>' (span.dual.c.cod f)) = \<chi>' f"
     and nt_not:"\<And> f. \<not> span.dual.c.arr f \<Longrightarrow> \<chi>' f = None"
      using 1[unfolded cone_def natural_transformation_def natural_transformation_axioms_def]
      by (auto simp:constant_functor_def)
    note nt = nt[OF span.dual.has_dom_cod_arrI(3)[OF cospan_object cospan_object],of "Arrow _ _ ()",unfolded Arrow.sel]
    define D' where D': "D' = source (the a')"
    note [simp] = span_valids[THEN span_dom_cod(1)] span_valids[THEN span_dom_cod(2)]
    have D [intro]:"C.vo D'" "a' = Some (C.ID D')"
     using cf unfolding D' constant_functor_axioms_def by auto
    note [simp] = constant_functor.map_def[OF cf(2),unfolded D]
    { fix x y
      assume spx:"span.dual.va x y ()"
      have "\<chi>' (Some (Arrow x y ())) \<noteq> None"
      using nt(2)[OF spx] span.dual.dom_cod_simps[OF cospan_object cospan_object spx,simplified]
      by (cases x;cases y,auto simp: C.c.cod_char split:if_splits)
    }
    from cospan_valids[THEN this]
    obtain h' k' D1 D2 D3 D4 D5 X' Y' Z1 Z2 Z3 diag1 diag2 diag3
      where hk [simp]:
      "\<chi>' (Some (Arrow finite_3.a\<^sub>2 finite_3.a\<^sub>2 ())) = Some (Arrow D1 X' h')"
      "\<chi>' (Some (Arrow finite_3.a\<^sub>3 finite_3.a\<^sub>3 ())) = Some (Arrow D2 Y' k')"
      "\<chi>' (Some (Arrow finite_3.a\<^sub>1 finite_3.a\<^sub>1 ())) = Some (Arrow D3 Z1 diag1)"
      "\<chi>' (Some (Arrow finite_3.a\<^sub>2 finite_3.a\<^sub>1 ())) = Some (Arrow D4 Z2 diag2)"
      "\<chi>' (Some (Arrow finite_3.a\<^sub>3 finite_3.a\<^sub>1 ())) = Some (Arrow D5 Z3 diag3)"
      unfolding not_None_eq
      by (metis (mono_tags, lifting) Arrow.collapse)
    have D1 [simp]:"D1 = D'" "X' = X"
      using nt(1,2)[OF cospan_valids(4)] by (auto simp:C.c.dom_char op_arr_def D split:if_splits)
    have D2 [simp]:"D2 = D'" "Y' = Y"
      using nt(1,2)[OF cospan_valids(5)] by (auto simp:C.c.dom_char op_arr_def D split:if_splits)
    have D3 [simp]:"D3 = D'" "Z1 = Z"
      using nt(1,2)[OF cospan_valids(1)] by (auto simp:C.c.dom_char op_arr_def D split:if_splits)
    have D4 [simp]:"D4 = D'" "Z2 = Z"
      using nt(1,2)[OF cospan_valids(2)] by (auto simp:C.c.dom_char op_arr_def D split:if_splits)
    have D5 [simp]:"D5 = D'" "Z3 = Z"
      using nt(1,2)[OF cospan_valids(3)] by (auto simp:C.c.dom_char op_arr_def D split:if_splits)
    have hk:"C.cmp D' X Z h' f = C.cmp D' Y Z k' g \<and> C.va D' X h' \<and> C.va D' Y k'"
      using cospan_valids(1-3)[THEN nt(3)] cospan_valids(1-3)[THEN nt(4)]
      by (auto simp:op_arr_def D split:if_splits)
    have "\<exists>!u. C.va D' D u \<and> C.cmp D' D X u h = h' \<and> C.cmp D' D Y u k = k'"
      using hk D is_universal by auto
    then obtain u where u[intro]:
      "C.va D' D u" "C.cmp D' D X u h = h'" "C.cmp D' D Y u k = k'"
      "\<And> y. C.va D' D y \<Longrightarrow> C.cmp D' D X y h = h' \<Longrightarrow> C.cmp D' D Y y k = k' \<Longrightarrow> y = u"
      unfolding Ex1_def by blast
    have "C.cmp D' X Z h' f = C.cmp D' D Z u diagonal"
      unfolding u(2)[symmetric] C.cmp_associative[OF u(1) valid_arr(3) valid_arr(1),unfolded is_cone]
      using refl.
    hence [simp] :
        "diag1 = C.cmp D' D Z u diagonal"
        "diag2 = C.cmp D' D Z u diagonal"
        "diag3 = C.cmp D' D Z u diagonal"
      using nt(3,4)[OF cospan_valids(2)] nt(3,4)[OF cospan_valids(3)] unfolding hk D
      by (auto simp: op_arr_def split:if_splits)
    note [simp] = C.dom_cod_simps[OF D(1) valid_obj(4) u(1)]
    note [intro] = cone.cone_axioms
    show ?case unfolding D proof
      let ?a = "Some (Arrow D' D u)"
      { fix x :: "(Enum.finite_3, unit) Arrow option"
        have "co.diagram.cones_map ?a \<chi> x = \<chi>' x" proof(cases x)
          case None thus ?thesis using nt_not by auto next
          case (Some x') obtain s t m where x:"x' = (Arrow s t m)" using Arrow.exhaust.
          show ?thesis unfolding x Some by(cases s;cases t;cases m,auto simp:nt_not)
        qed }
      thus "?a \<in> C.c.hom (Some (C.ID D')) (Some (C.ID D)) \<and> co.diagram.cones_map ?a \<chi> = \<chi>'" by auto
    fix f assume "f \<in> C.c.hom (Some (C.ID D')) (Some (C.ID D)) \<and> co.diagram.cones_map f \<chi> = \<chi>'"
    hence assms:"C.c.arr f" "C.c.dom f = Some (C.ID D')" "C.c.cod f = Some (C.ID D)"
                "co.diagram.cones_map f \<chi> = \<chi>'" by auto
    from assms(2,3) obtain u' where u' [simp]:"f = Some (Arrow D' D u')"
      by (cases "the f",auto simp:C.c.dom_char split:if_splits)
    have arrf [intro]:"C.c.arr (Some (Arrow D' D u'))" using assms(1)[unfolded u'].
    hence f_char:"\<And> j. (if span.va (target (the j)) (source (the j)) () \<and> j \<noteq> None
                         then C.c.comp (\<chi> j) f else None) = \<chi>' j"
      and diacone:"co.diagram.cone (C.c.cod (Some (Arrow D' D u'))) \<chi>"
      using assms(4) by auto
    { fix s t
      have "span.va t s () \<Longrightarrow> C.c.comp (\<chi> (C.arr s t ())) f = \<chi>' (C.arr s t ())"
        using f_char[of "Some (Arrow s t ())"] by (auto split:if_splits) }
    note f_char = this
    have [simp]: "u' = u" proof(standard,goal_cases)
      case 1
      then show ?case using arrf by auto
    next
      case 2 
      then show ?case using f_char[OF span_valids(4),unfolded u',simplified]
        by (auto split:if_splits)
    next
      case 3
      then show ?case using f_char[OF span_valids(5),unfolded u',simplified]
        by (auto split:if_splits)
    qed
    show "f = Some (Arrow D' D u)" using u' by auto
  qed qed
end

locale arrow_pushout =
  C: arrow_category Cat
  for Cat :: "('o, 'm) Category" and X Y Z D f g h k +
  assumes valid_obj[intro]:"C.vo X" "C.vo Y" "C.vo Z" "C.vo D"
  and valid_arr[intro]: "C.va Z X f" "C.va Z Y g" "C.va X D h" "C.va Y D k"
  and is_cone:"C.cmp Z X D f h = C.cmp Z Y D g k"
  and is_universal: "C.cmp Z X D' f h' = C.cmp Z Y D' g k' \<and> C.vo D' \<and> C.va X D' h' \<and> C.va Y D' k'
                 \<Longrightarrow> \<exists>!u. C.va D D' u \<and> C.cmp X D D' h u = h' \<and> C.cmp Y D D' k u = k'"
begin
  interpretation arrow_category_with_dual Cat by standard
  interpretation pb : arrow_pullback dual apply standard using is_cone is_universal by auto
  sublocale pushout : pullback dual.c.comp pb.co.Functor "Some (C.ID D)" pb.\<chi>
    using pb.pullback.pullback_axioms by auto
end