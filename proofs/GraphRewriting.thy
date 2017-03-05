theory GraphRewriting
imports
  Limit
begin

datatype ('l,'v) labeled_graph = LG (edges:"('l \<times> 'v \<times> 'v) set")

definition constant_respecting where
  "constant_respecting K G \<equiv> \<exists> \<alpha>. inj_on \<alpha> K \<and> (\<forall> k\<in>K. \<forall> v1 v2. (k,v1,v2) \<in> edges G \<longleftrightarrow> (\<alpha> k = v1 \<and> \<alpha> k = v2))"

definition empty_graph where
  "empty_graph \<equiv> LG {}"

lemma constant_respecting_empty_graph: "constant_respecting K empty_graph \<longleftrightarrow> K = {}"
unfolding constant_respecting_def empty_graph_def by auto

abbreviation entire where
  "entire R \<equiv> Domain R = UNIV"

lemma entire_compose[simp]:
  assumes "entire h1" "entire h2"
  shows "x \<in> Domain (h1 O h2)"
proof -
  obtain y z where "(x,y) \<in> h1" "(y,z) \<in> h2" using assms by blast
  thus ?thesis by auto
qed

datatype ('l,'v1,'v2) pre_graph_homomorphism
  = GH (source:"('l,'v1) labeled_graph")
       (target:"('l,'v2) labeled_graph")
       (homomp:"('v1\<times>'v2) set")

definition edge_preserving where
  "edge_preserving h e1 e2 \<equiv> (\<forall> (k,v1,v2) \<in> e1. \<forall> v1' v2'. ((v1, v1') \<in> h \<and> (v2,v2') \<in> h) \<longrightarrow> (k,v1',v2') \<in> e2)"

lemma edge_preserving_atomic:
  assumes "(v1, v1') \<in> h1" "(v2, v2') \<in> h1" "edge_preserving h1 e1 e2" "(k, v1, v2) \<in> e1"
  shows "(k, v1', v2') \<in> e2"
using assms unfolding edge_preserving_def by auto

lemma compose_preserves_edge_preserving[intro]:
  assumes "edge_preserving h1 e1 e2" "edge_preserving h2 e2 e3"
  shows "edge_preserving (h1 O h2) e1 e3" unfolding edge_preserving_def
proof(standard,standard,standard,standard,standard,standard,goal_cases)
  case (1 _ k _ v1 v2 v1'' v2'')
  hence 1:"(k, v1, v2) \<in> e1" "(v1, v1'') \<in> h1 O h2" "(v2, v2'') \<in> h1 O h2" by auto
  then obtain v1' v2' where
    v:"(v1,v1') \<in> h1" "(v1',v1'') \<in> h2" "(v2,v2') \<in> h1" "(v2',v2'') \<in> h2" by auto
  from edge_preserving_atomic[OF v(1,3) assms(1) 1(1)]
       edge_preserving_atomic[OF v(2,4) assms(2)]
  show ?case by metis
qed

lemma edge_preserving_Id[intro]:
  "edge_preserving Id x x"
unfolding edge_preserving_def by auto

fun is_graph_homomorphism where
  "is_graph_homomorphism (GH s t h) = (entire h \<and> edge_preserving h (edges s) (edges t))"

fun id_on where
"id_on v = GH v v Id"

lemma id_is_graph_homomorphism:
  "is_graph_homomorphism (id_on v)"
by(cases "id_on v";auto)

typedef (overloaded) ('l,'v) graph_homomorphism
  = "{ h :: ('l,'v,'v) pre_graph_homomorphism. is_graph_homomorphism h}"
  morphisms get_GH IsGH
proof -
  have "is_graph_homomorphism (GH empty_graph empty_graph Id)" by (auto simp:edge_preserving_def)
  thus ?thesis by blast
qed
setup_lifting type_definition_graph_homomorphism

fun pre_graph_homomorphism_comp where
  "pre_graph_homomorphism_comp (GH s1 t1 h1) (GH s2 t2 h2)
    = (if t1 = s2 then Some (GH s1 t2 (h1 O h2)) else None)"

lemma pre_graph_homomorphism_comp_assoc :
  "Option.bind (pre_graph_homomorphism_comp b c) (    pre_graph_homomorphism_comp a) =
   Option.bind (pre_graph_homomorphism_comp a b) (\<lambda>x. pre_graph_homomorphism_comp x c)"
by(cases a;cases b;cases c;auto)

lemma pre_graph_homomorphism_comp_fits [simp]:
  "(\<exists> y. pre_graph_homomorphism_comp a b = Some y) \<longleftrightarrow> source b = target a"
  by (cases a;cases b;auto)

lemma pre_graph_homomorphism_preserves_graph_homomorphism:
  assumes "is_graph_homomorphism gh1" "is_graph_homomorphism gh2"
  shows "pred_option is_graph_homomorphism (pre_graph_homomorphism_comp gh1 gh2)"
  using assms by(cases gh1,cases gh2,auto)

lemma pre_graph_homomorphism_id [simp]:
  "pre_graph_homomorphism_comp a (GH (target a) (target a) Id) = Some a"
  "pre_graph_homomorphism_comp (GH (source a) (source a) Id) a = Some a"
by(cases a,auto)+

lift_definition graph_homomorphism_comp ::
   "('l,'v) graph_homomorphism \<Rightarrow> ('l,'v) graph_homomorphism \<Rightarrow> ('l,'v) graph_homomorphism option"
   is pre_graph_homomorphism_comp by (fact pre_graph_homomorphism_preserves_graph_homomorphism)

lift_definition src :: "('l,'v) graph_homomorphism \<Rightarrow> ('l,'v) labeled_graph" is source.
lift_definition tgt :: "('l,'v) graph_homomorphism \<Rightarrow> ('l,'v) labeled_graph" is target.
lift_definition fnc :: "('l,'v) graph_homomorphism \<Rightarrow> 'v rel" is homomp.
lift_definition idt :: "('l,'v) labeled_graph \<Rightarrow> ('l,'v) graph_homomorphism" is id_on by auto

lemma exists_subset :
  assumes "(\<exists> a. P1 a) = (\<exists> a. P2 a)"
        "\<And> a. P1 a \<Longrightarrow> a \<in> S1" "\<And> a. P2 a \<Longrightarrow> a \<in> S2"
  shows "(\<exists> a \<in> S1. P1 a) = (\<exists> a \<in> S2. P2 a)"
using assms by auto
lemma exists_subset_left :
  assumes "(\<exists> a. P1 a) = P2"
        "\<And> a. P1 a \<Longrightarrow> a \<in> S1"
  shows "(\<exists> a \<in> S1. P1 a) = P2"
using assms by auto

lemma graph_homomorphism_comp_fits [simp]:
  "(\<exists> y. graph_homomorphism_comp a b = Some y) \<longleftrightarrow> src b = tgt a"
  apply(transfer)
  apply(intro exists_subset_left[OF pre_graph_homomorphism_comp_fits])
  unfolding mem_Collect_eq
  using pre_graph_homomorphism_preserves_graph_homomorphism by fastforce

lemma src_tgt_idt_simps[simp]:
  "src (idt v) = v"
  "tgt (idt v) = v"
by(transfer,auto)+

lemma graph_homomorphism_comp_assoc :
  "Option.bind (graph_homomorphism_comp b c) (    graph_homomorphism_comp a) =
   Option.bind (graph_homomorphism_comp a b) (\<lambda>x. graph_homomorphism_comp x c)"
  by(transfer,rule pre_graph_homomorphism_comp_assoc)

definition "cmp" where
  "cmp l r \<equiv> Option.bind l (Option.bind r o graph_homomorphism_comp)"

lemma cmp_assoc[simp]:
  "cmp a (cmp b c) = cmp (cmp a b) c"
  unfolding cmp_def o_def bind_assoc using graph_homomorphism_comp_assoc
  by(intro Option.bind_cong[OF refl],cases c,auto)

lemma cmp_none:
  "\<exists>!n. \<forall>f. cmp n f = n \<and> cmp f n = n"
  proof (* we start by showing uniqueness part *)
    fix n assume "\<forall>f. cmp n f = n \<and> cmp f n = n"
    hence "cmp None n = n" by auto
    thus "n = None" unfolding cmp_def by auto
  qed (auto simp:cmp_def o_def)

interpretation cmp_magma : partial_magma cmp
  by(unfold_locales,intro cmp_none)

lemma null_is_None[simp]:"cmp_magma.null = None"
  unfolding cmp_magma.null_def
  by (rule the1_equality[OF cmp_none],auto simp:cmp_def o_def)

definition cmp_cod where "cmp_cod \<equiv> map_option tgt"
definition cmp_dom where "cmp_dom \<equiv> map_option src"
definition cmp_f   where "cmp_f   \<equiv> map_option fnc"
definition cmp_id  where "cmp_id  \<equiv> map_option idt"

lemma cmp_exists_simps[simp]:
  "(\<exists>ya. cmp_id y = Some ya) \<longleftrightarrow> (\<exists> ya. y = Some ya)"
  "(\<exists>ya. cmp_dom v = Some ya) \<longleftrightarrow> (\<exists> ya. v = Some ya)"
  "(\<exists>ya. cmp_cod v = Some ya) \<longleftrightarrow> (\<exists> ya. v = Some ya)"
  by (auto simp:cmp_dom_def cmp_cod_def cmp_id_def)

lemma cmp_id_simps[simp]:
  "cmp_dom (cmp_id a) = a"
  "cmp_cod (cmp_id a) = a"
  by (cases a;auto simp:cmp_dom_def cmp_cod_def cmp_id_def)+

lemma defined_arrow[simp]:
  "(\<exists> y. cmp h g = Some y) \<longleftrightarrow> (h \<noteq> None \<and> g \<noteq> None \<and> cmp_cod h = cmp_dom g)"
  by (cases h;cases g;auto simp:cmp_def cmp_cod_def cmp_dom_def)

lemma cmp_idt[simp]:
  "tgt a = v \<Longrightarrow> cmp (Some a) (Some (idt v)) = Some a"
  "src a = v \<Longrightarrow> cmp (Some (idt v)) (Some a) = Some a"
unfolding cmp_def by(transfer,auto)+

lemma cmp_magma_unit[dest]: (* TODO: not used, turn into elim rule or remove. *)
  assumes "cmp_magma.unit a"
    shows "cmp_cod a = cmp_dom a" (is ?e) and "cmp_id (cmp_cod a) = a" (is ?i)
proof-
  have ie:"?i \<and> ?e" proof(cases a)
    case None thus ?thesis unfolding cmp_cod_def cmp_dom_def cmp_id_def by auto next
    case (Some a')
    from assms[unfolded cmp_magma.unit_def Some]
    have f:"\<And>f. cmp f (Some a') \<noteq> None \<Longrightarrow> cmp f (Some a') = f" by auto
    from f[of "Some (idt (src a'))"]
    have src:"idt (src a') = a'" by auto
    hence tgt:"tgt a' = src a'" by (metis src_tgt_idt_simps(2))
    show ?thesis using src tgt unfolding cmp_cod_def cmp_dom_def cmp_id_def Some by auto
  qed
  from ie show ?i by blast
  from ie show ?e by blast
qed

lemma cmp_magma_unitI[intro]: shows "cmp_magma.unit (cmp_id v)"
by (cases v;auto simp: cmp_magma.unit_def cmp_id_def cmp_cod_def cmp_dom_def)

lemma cmp_magma_has_domE[simp]:
  "cmp_magma.has_dom x \<longleftrightarrow> x \<noteq> None" unfolding cmp_magma.has_dom_def
proof
  assume "x \<noteq> None" then obtain y where y:"x = Some y" by auto
  have "cmp_magma.unit (cmp_id (cmp_cod x))"
       "cmp x (cmp_id (cmp_cod x)) \<noteq> cmp_magma.null" by (auto simp:y)
  thus "\<exists>a. cmp_magma.unit a \<and> cmp x a \<noteq> cmp_magma.null" by blast
qed auto

lemma cmp_magma_has_codE[simp]:
  "cmp_magma.has_cod x \<longleftrightarrow> x \<noteq> None" unfolding cmp_magma.has_cod_def
proof
  assume "x \<noteq> None" then obtain y where y:"x = Some y" by auto
  have "cmp_magma.unit (cmp_id (cmp_dom x))"
       "cmp (cmp_id (cmp_dom x)) x \<noteq> cmp_magma.null" by (auto simp:y)
  thus "\<exists>a. cmp_magma.unit a \<and> cmp a x \<noteq> cmp_magma.null" by blast
qed auto

lemma defined_graph_homomorphism_comp:
  assumes "graph_homomorphism_comp h g = Some y"
    shows "tgt h = src g" "src y = src h" "tgt y = tgt g"
proof -
  have r:"tgt h = src g \<and> src y = src h \<and> tgt y = tgt g"
  using assms
  proof(transfer,goal_cases)
    case (1 h g y) thus ?case by(cases h;cases g;cases y;auto split:if_split_asm)
  qed
  show "tgt h = src g" using r by blast
  show "src y = src h" using r by blast
  show "tgt y = tgt g" using r by blast
qed

lemma cmp_dom_cod_cmp_simps[simp]:
  "cmp_cod g = cmp_dom h \<Longrightarrow> cmp_dom (cmp g h) = cmp_dom g"
  "cmp_cod g = cmp_dom h \<Longrightarrow> cmp_cod (cmp g h) = cmp_cod h"
  using defined_graph_homomorphism_comp(2,3)[of "the g" "the h" "the (cmp g h)"]
  apply (cases h,auto simp:cmp_dom_def cmp_cod_def cmp_def o_def)
  apply (metis graph_homomorphism_comp_fits option.collapse option.simps(3))
  apply (cases h,auto simp:cmp_dom_def cmp_cod_def cmp_def o_def)
  by (metis graph_homomorphism_comp_fits option.collapse option.simps(3))

interpretation cmp_category : category cmp by(standard,auto)



end