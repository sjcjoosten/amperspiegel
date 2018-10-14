theory StandardRules
imports StandardModels RuleSemanticsConnection
begin

(* Remark at Definition 16*)
lemma conflict_free:
":G:\<lbrakk>A_Lbl l\<rbrakk> = {} \<longleftrightarrow> (\<forall> (l',x,y)\<in>edges G. l' \<noteq> l)"
  by (auto simp:getRel_def)

(* Definition 17 *)
(* It's unlikely that we wish to use the top rule for any symbol except top,
   but we give the relation symbol as an argument just for consistency with the identity rules *)
definition top_rule :: "'l \<Rightarrow> ('l,nat) Graph_PreRule" where	
"top_rule t = (LG {} {0,1},LG {(t,0,1)} {0,1})"	
(* Definition 18 *)
definition nonempty_rule :: "('l,nat) Graph_PreRule" where
"nonempty_rule = (LG {} {},LG {} {0})"	

(* Since the equivalence rules might be useful for other equivalence relations,
   we give the relation symbol as an argument *)
definition reflexivity_rule :: "'l \<Rightarrow> ('l,nat) Graph_PreRule" where
"reflexivity_rule t = (LG {} {0},LG {(t,0,0)} {0})"	

definition symmetry_rule :: "'l \<Rightarrow> ('l,nat) Graph_PreRule" where
"symmetry_rule t = (transl_rule (A_Cnv (A_Lbl t) \<sqsubseteq> A_Lbl t))"
definition transitive_rule :: "'l \<Rightarrow> ('l,nat) Graph_PreRule" where
"transitive_rule t = (transl_rule (A_Cmp (A_Lbl t) (A_Lbl t) \<sqsubseteq> A_Lbl t))"
definition congruence_rule :: "'l \<Rightarrow> 'l \<Rightarrow> ('l,nat) Graph_PreRule" where
"congruence_rule t l = (transl_rule (A_Cmp (A_Cmp (A_Lbl t) (A_Lbl l)) (A_Lbl t) \<sqsubseteq> A_Lbl l))"
abbreviation congruence_rules :: "'l \<Rightarrow> 'l set \<Rightarrow> ('l,nat) Graph_PreRule set"
    where
"congruence_rules t L \<equiv> congruence_rule t ` L"

lemma are_rules[intro]:
"graph_rule nonempty_rule"	
"graph_rule (top_rule t)"	
"graph_rule (reflexivity_rule i)"	
  unfolding reflexivity_rule_def top_rule_def nonempty_rule_def is_graph_homomorphism_def	
  by auto

lemma non_empty_rule_non_empty[dest]:
  assumes "maintained nonempty_rule G" "graph G" 
  shows "\<exists> x. x \<in> vertices G"
proof -
  have "is_graph_homomorphism (fst nonempty_rule) G {}"
    using assms(1,2) unfolding is_graph_homomorphism_def2 nonempty_rule_def by auto
  with assms[unfolded maintained_def] have "extensible nonempty_rule G {}" by auto
  then obtain g where hom:"is_graph_homomorphism (snd nonempty_rule) G g"
    unfolding extensible_def by blast
  hence "0 \<in> Domain g" unfolding is_graph_homomorphism_def nonempty_rule_def prod.sel by auto
  then obtain y where "(0,y) \<in> g" by auto
  with hom have "y\<in> vertices G" unfolding is_graph_homomorphism_def by auto
  thus ?thesis by auto
qed

lemma top_rule_full[dest]:
  assumes "maintained (top_rule t) G" "graph G"
  shows "x \<in> vertices G \<and> y \<in> vertices G \<longleftrightarrow> (x,y) \<in> getRel t G"
proof
  assume a:"x \<in> vertices G \<and> y \<in> vertices G"
  let ?f = "{(0,x),(1,y)}" let ?R = "top_rule t"
  have "is_graph_homomorphism (fst ?R) G ?f"
    using assms a unfolding is_graph_homomorphism_def top_rule_def
    by (cases G,auto simp:univalent_def)
  with assms[unfolded maintained_def] have "extensible ?R G ?f" by auto
  then obtain g where hom:"is_graph_homomorphism (snd ?R) G g"
    and agr:"agree_on (fst ?R) ?f g"
    unfolding extensible_def by blast
  with a have g:"(0,x) \<in> g" "(1,y) \<in> g" unfolding agree_on_def top_rule_def by auto
  have "(t,0,1)\<in>edges (snd ?R)" unfolding top_rule_def by auto
  with g have "(t,x,y)\<in>edges (map_graph g (snd ?R))" unfolding map_graph_def on_triple_def by auto
  with hom[unfolded is_graph_homomorphism_def2 graph_union_iff] have "(t,x,y)\<in>edges G" by auto
  thus "(x,y) \<in> getRel t G" by (auto simp: getRel_def) next
  assume "(x, y) \<in> getRel t G"
  with assms(2) show "x \<in> vertices G \<and> y \<in> vertices G" unfolding getRel_def by auto 
qed

(* Remark just before Lemma 7: if I is an identity, it maintains the identity rules *)
lemma ident_rel_refl:
  assumes "graph G" "ident_rel idt G"
  shows "maintained (reflexivity_rule idt) G"
  unfolding reflexivity_rule_def
proof(rule maintainedI) fix f
  assume "is_graph_homomorphism (LG {} {0::nat}) G f"
  hence f:"Domain f = {0}" "graph G" "f `` {0} \<subseteq> vertices G" "univalent f"
    unfolding is_graph_homomorphism_def by force+
  with assms(2) have "edge_preserving f {(idt, 0, 0)} (edges G)" unfolding edge_preserving
    by (auto simp:getRel_def set_eq_iff image_def)
  with f have "is_graph_homomorphism (LG {(idt, 0, 0)} {0}) G f"
              "agree_on (LG {} {0}) f f" using assms
    unfolding is_graph_homomorphism_def labeled_graph.sel agree_on_def univalent_def
    by auto
  then show "extensible (LG {} {0}, LG {(idt, 0, 0)} {0}) G f"
    unfolding extensible_def prod.sel by auto
qed

lemma
  assumes "ident_rel idt G"
  shows ident_rel_trans:"maintained (transitive_rule idt) G"
    and ident_rel_symm :"maintained (symmetry_rule idt) G"
    and ident_rel_cong :"maintained (congruence_rule idt l) G"
  unfolding transitive_rule_def symmetry_rule_def congruence_rule_def
  by(intro maintained_holds,insert assms,force)+

(* Definition 19 *)
definition identity_rules ::
  "'a Standard_Constant set \<Rightarrow> (('a Standard_Constant, nat) Graph_PreRule) set" where
  "identity_rules L \<equiv> {reflexivity_rule S_Idt,transitive_rule S_Idt,symmetry_rule S_Idt}
                       \<union> congruence_rules S_Idt L"

(* Implicit properties of Definition 19 *)
lemma
  assumes g[intro]:"graph (G :: ('a, 'b) labeled_graph)"
  shows reflexivity_rule: "maintained (reflexivity_rule l) G \<Longrightarrow> refl_on (vertices G) (getRel l G)"
    and transitive_rule: "maintained (transitive_rule l) G \<Longrightarrow> trans (getRel l G)"
    and symmetry_rule: "maintained (symmetry_rule l) G \<Longrightarrow> sym (getRel l G)"
proof -
  { from assms have gr:"getRel l G \<subseteq> vertices G \<times> vertices G" by (auto simp:getRel_def)
    assume m:"maintained (reflexivity_rule l) G" (is "maintained ?r G")
    note [simp] = reflexivity_rule_def
    show r:"refl_on (vertices G) (getRel l G)"
    proof(rule refl_onI[OF gr]) fix x
      assume assm:"x \<in> vertices G"  define f where "f = {(0::nat,x)}"
      have "is_graph_homomorphism (fst ?r) G f" using assm
        by (auto simp:is_graph_homomorphism_def univalent_def f_def)
      from m[unfolded maintained_def] this 
      obtain g::"(nat\<times>'b) set"
        where g:"is_graph_homomorphism (snd ?r) G g"
                "agree_on (fst ?r) f g"
        unfolding extensible_def by blast
      have "\<And> n v. (n,v) \<in> g \<Longrightarrow> (n = 0) \<and> (v = x)" using g unfolding
        agree_on_def is_graph_homomorphism_def f_def by auto
      with g(2) have "g = {(0,x)}" unfolding agree_on_def f_def by auto
      with g(1) show "(x,x)\<in> getRel l G"
        unfolding is_graph_homomorphism_def edge_preserving getRel_def by auto
    qed
  }
  { assume m:"maintained (transitive_rule l) G"
    from m[unfolded maintained_holds_subset_iff[OF g] transitive_rule_def]
    show "trans (getRel l G)" unfolding trans_def by auto
  }
  { assume m:"maintained (symmetry_rule l) G"
    from m[unfolded maintained_holds_subset_iff[OF g] symmetry_rule_def]
    show "sym (getRel l G)" unfolding sym_def by auto
  }
qed

lemma equivalence:
  assumes gr:"graph G" and m:"maintainedA {reflexivity_rule I,transitive_rule I,symmetry_rule I} G"
  shows "equiv (vertices G) (getRel I G)"
proof(rule equivI)
  show "refl_on (vertices G) (getRel I G)" using m by(intro reflexivity_rule[OF gr],auto)
  show "sym (getRel I G)" using m by(intro symmetry_rule[OF gr],auto)
  show "trans (getRel I G)" using m by(intro transitive_rule[OF gr],auto)
qed

lemma congruence_rule:
 (* Transitivity is not needed for this proof, but it's more convenient to reuse in this form *)
  assumes g:"graph G"
      and mA:"maintainedA {reflexivity_rule I,transitive_rule I,symmetry_rule I} G"
      and m:"maintained (congruence_rule I l) G"
    shows "(\<lambda> v. getRel l G `` {v}) respects (getRel I G)" (is "?g1")
      and "(\<lambda> v. (getRel l G)\<inverse> `` {v}) respects (getRel I G)" (is "?g2")
proof -
  (* Both parts of this lemma are proved using roughly the same proof. *)
  note eq = equivalence[OF g mA]
  { fix y z
    assume aI:"(y, z)\<in>getRel I G"
    hence a2:"(z, y)\<in>getRel I G" using eq[unfolded equiv_def sym_def] by auto
    hence a3:"(z, z)\<in>getRel I G" "(y, y)\<in>getRel I G"
      using eq[unfolded equiv_def refl_on_def] by auto
    { fix x
      { assume al:"(y,x) \<in> getRel l G"
        hence "x \<in> vertices G" using g unfolding getRel_def by auto
        hence r:"(x,x) \<in> getRel I G" using eq[unfolded equiv_def refl_on_def] by auto
        note relcompI[OF relcompI[OF a2 al] r]
      } note yx = this
      { assume al:"(z,x) \<in> getRel l G"
        hence "x \<in> vertices G" using g unfolding getRel_def by auto
        hence r:"(x,x) \<in> getRel I G" using eq[unfolded equiv_def refl_on_def] by auto
        note relcompI[OF relcompI[OF aI al] r]
      } note zx = this
      from zx yx m[unfolded maintained_holds_subset_iff[OF g] congruence_rule_def]
      have "(y,x) \<in> getRel l G \<longleftrightarrow> (z,x) \<in> getRel l G" by auto
    } note v1 = this
    { fix x
      { assume al:"(x,y) \<in> getRel l G"
        hence "x \<in> vertices G" using g unfolding getRel_def by auto
        hence r:"(x,x) \<in> getRel I G" using eq[unfolded equiv_def refl_on_def] by auto
        note relcompI[OF relcompI[OF r al] aI]
      } note yx = this
      { assume al:"(x,z) \<in> getRel l G"
        hence "x \<in> vertices G" using g unfolding getRel_def by auto
        hence r:"(x,x) \<in> getRel I G" using eq[unfolded equiv_def refl_on_def] by auto
        note relcompI[OF relcompI[OF r al] a2]
      } note zx = this
      from zx yx m[unfolded maintained_holds_subset_iff[OF g] congruence_rule_def]
      have "(x,y) \<in> getRel l G \<longleftrightarrow> (x,z) \<in> getRel l G" by auto
    } note v2 = this
    from v1 v2
    have "getRel l G `` {y} = getRel l G `` {z}"
         "(getRel l G)\<inverse> `` {y} = (getRel l G)\<inverse> `` {z}" by auto
  }
  thus ?g1 ?g2 unfolding congruent_def by force+
qed

lemma identity_rules: (* Lemma 7 *)
  assumes "graph G"
          "maintainedA (identity_rules L) G"
          "fst ` edges G \<subseteq> L"
  shows "\<exists> f. f o f = f
         \<and> ident_rel S_Idt (map_graph_fn G f)
         \<and> subgraph (map_graph_fn G f) G"
proof -
  (* While this proof defines a concrete f, we only expose it using an existential quantifier.
     The reason is that the f of our choice is non-constructive,
     and its definition relies on the axiom of choice.
     In fact, this theorem applies to the infinite case too,
     which means that it's probably equivalent to the axiom of choice.
     We therefore have no hopes of giving an executable concrete f here.
     In the implementation, we will be able to use finiteness of G (which is not required here),
     and therefore we can construct an f with these properties again.
     Unfortunately, this does mean doing roughly the same proof twice. *)
  have ma:"maintainedA {reflexivity_rule S_Idt, transitive_rule S_Idt, symmetry_rule S_Idt} G"
    using assms(2) by (auto simp:identity_rules_def)
  note equiv = equivalence[OF assms(1) this]
  { fix l x y
    assume "(x, y) \<in> getRel l G" hence l:"l \<in> L" using assms(3) unfolding getRel_def by auto
    have r1:"(\<lambda>v. getRel l G `` {v}) respects getRel S_Idt G"
      apply(intro congruence_rule[OF assms(1) ma])
      using assms(2) l unfolding identity_rules_def by auto
    have r2:"(\<lambda>v. (getRel l G)\<inverse> `` {v}) respects getRel S_Idt G"
      apply(intro congruence_rule[OF assms(1) ma])
      using assms(2) l unfolding identity_rules_def by auto
    note congr = r1 r2
  } note congr = this
  define P where P:"P = (\<lambda> x y. y \<in> getRel S_Idt G `` {x})"
  { fix x
    assume a:"getRel S_Idt G `` {x} \<noteq> {}"
    hence "\<exists> y. P x y" unfolding P by auto
    hence p:"P x (Eps (P x))" unfolding some_eq_ex by auto
    { fix y
      assume b:"P x y"
      hence "(x,y) \<in> getRel S_Idt G" unfolding P by auto
      from equiv_class_eq[OF equiv this]
      have "getRel S_Idt G `` {x} = getRel S_Idt G `` {y}".
    } note u = this[OF p]
    have "getRel S_Idt G `` {Eps (P x)} = getRel S_Idt G `` {x}"
      unfolding u by (fact refl)
    hence "Eps (P (Eps (P x))) = Eps (P x)" unfolding P by auto
  } note P_eq = this
  define f where f:"f = (\<lambda> x. (if getRel S_Idt G `` {x} = {} then x else (SOME y. P x y)))"
  have "(f \<circ> f) x = f x" for x proof(cases "getRel S_Idt G `` {x} = {}")
    case False
    then show ?thesis using P_eq by (simp add:o_def f)
  qed (auto simp:o_def f)
  hence idemp: "f o f = f" by auto
 
  from equivE equiv have refl:"refl_on (vertices G) (getRel S_Idt G)" by auto
  hence [intro]:"x \<in> vertices G \<Longrightarrow> (x, x) \<in> getRel S_Idt G" for x unfolding refl_on_def by auto
  hence vert_P:"x \<in> vertices G \<Longrightarrow> (x, Eps (P x)) \<in> getRel S_Idt G" for x
     unfolding P getRel_def by (metis tfl_some Image_singleton_iff getRel_def)
  have r1:"x \<in> vertices G \<longleftrightarrow> P x x" for x using refl unfolding refl_on_def P by auto
  have r2[simp]:"getRel S_Idt G `` {x} = {} \<longleftrightarrow> x \<notin> vertices G" for x
    using refl assms(1) unfolding refl_on_def by auto
  { fix x y assume "(S_Idt,x,y)\<in> edges G"
    hence "(x,y) \<in> getRel S_Idt G" unfolding getRel_def by auto
    hence "getRel S_Idt G `` {x} = getRel S_Idt G `` {y}"
      using equiv_class_eq[OF equiv] by metis
    hence "Eps (P x) = Eps (P y)" unfolding P by auto
  } note idt_eq = this
  have ident:"ident_rel S_Idt (map_graph_fn G f)"
  proof(rule ident_relI,goal_cases)
    case (1 x) thus ?case unfolding f by auto
  next case (2 x y) thus ?case unfolding getRel_def by (auto simp:f intro!:idt_eq)
  next case (3 x y) thus ?case unfolding getRel_def by auto
  qed

  { fix l x y
    assume a:"(l,x,y) \<in> edges G" "x \<in> vertices G" "y \<in> vertices G"
    hence f:"(f x, x) \<in> getRel S_Idt G" "(f y, y) \<in> getRel S_Idt G" 
      using vert_P equivE[OF equiv] sym_def unfolding f by auto
    from a have gr:"(x, y) \<in> getRel l G" unfolding getRel_def by auto
    from congruentD[OF congr(1)[OF gr] f(1)] congruentD[OF congr(2)[OF gr] f(2)] a(1)
    have "(l,f x, f y) \<in> edges G" unfolding set_eq_iff getRel_def by auto
  } note gu1 = this
  { fix x assume a: "x \<in> vertices G"
    with vert_P have "(x,Eps (P x)) \<in> getRel S_Idt G" by auto
    hence "Eps (P x) \<in> vertices G" using assms(1) unfolding getRel_def by auto
    hence "f x \<in> vertices G" using a unfolding f by auto
  } note gu2 = this
  have "graph_union (map_graph_fn G f) G = G"
    using gu1 gu2 assms(1) unfolding graph_union_def by(cases G,auto)
  hence subg: "subgraph (map_graph_fn G f) G"
    unfolding subgraph_def using assms(1) by auto
  from idemp ident subg show ?thesis by auto
qed

lemma idemp_embedding_maintained_preserved:
  assumes subg:"subgraph (map_graph_fn G f) G" and f:"\<And> x. x\<in>vertices G \<Longrightarrow> (f o f) x = f x"
      and maint:"maintained r G"
    shows "maintained r (map_graph_fn G f)"
proof -
  { fix h assume hom_h:"is_graph_homomorphism (fst r) (map_graph_fn G f) h"
    from subgraph_preserves_hom[OF subg this] maint[unfolded maintained_def extensible_def]
    obtain g where g:"is_graph_homomorphism (snd r) G g"
                     "agree_on (fst r) h g" by blast
    { fix v x
      have subs:"h `` {v} \<subseteq> vertices (map_graph_fn G f)" 
        using hom_h[unfolded is_graph_homomorphism_def] by auto
      assume "v\<in>vertices (fst r)" and x:"(v, x) \<in> g"
      hence "g `` {v} = h `` {v}" using g(2)[unfolded agree_on_def,rule_format,of v] by auto
      hence "g `` {v} \<subseteq> vertices (map_graph_fn G f)" using subs by auto
      hence x2:"x \<in> vertices (map_graph_fn G f)" using x by auto
      then obtain y where "x = f y" "y \<in> vertices G" by auto
      hence f:"f x = x" using f x2 unfolding o_def by metis
      from x2 subgraph_subset[OF subg] have "(x, f x) \<in> on_graph G f" by auto
      with x have "(v, x) \<in> g O on_graph G f" "f x = x" unfolding f by auto
    }
    hence agr:"agree_on (fst r) h (g O on_graph G f)"
      using g(2) unfolding agree_on_def by auto
    have "extensible r (map_graph_fn G f) h"
      unfolding extensible_def using is_graph_homomorphism_on_graph[OF g(1)] agr by blast
  }
  thus ?thesis unfolding maintained_def by blast
qed

abbreviation const_exists where
"const_exists c \<equiv> transl_rule (\<top> \<sqsubseteq> A_Cmp (A_Cmp \<top> (A_Lbl (S_Const c))) \<top>)"
abbreviation const_exists_rev where
"const_exists_rev c \<equiv> transl_rule (A_Cmp (A_Cmp (A_Lbl (S_Const c)) \<top>) (A_Lbl (S_Const c)) \<sqsubseteq> A_Lbl (S_Const c))"
abbreviation const_prop where
"const_prop c \<equiv> transl_rule (A_Lbl (S_Const c) \<sqsubseteq> \<one>)"
abbreviation const_disj where
"const_disj c\<^sub>1 c\<^sub>2 \<equiv> transl_rule (A_Cmp (A_Lbl (S_Const c\<^sub>1)) (A_Lbl (S_Const c\<^sub>2)) \<sqsubseteq> \<bottom>)"

definition constant_rules where
"constant_rules C \<equiv> const_exists ` C \<union> const_exists_rev ` C \<union> const_prop ` C
                  \<union> {const_disj c\<^sub>1 c\<^sub>2 | c\<^sub>1 c\<^sub>2. c\<^sub>1 \<in> C \<and> c\<^sub>2 \<in> C \<and> c\<^sub>1 \<noteq> c\<^sub>2}"

lemma constant_rules_empty[simp]:
  "constant_rules {} = {}" by (auto simp:constant_rules_def)

abbreviation standard_rules :: "'a set \<Rightarrow> 'a Standard_Constant set \<Rightarrow> (('a Standard_Constant, nat) labeled_graph \<times> ('a Standard_Constant, nat) labeled_graph) set"
  where
"standard_rules C L \<equiv> constant_rules C \<union> identity_rules L \<union> {top_rule S_Top,nonempty_rule}"

lemma constant_rules_mono:
  assumes "C\<^sub>1 \<subseteq> C\<^sub>2"
  shows "constant_rules C\<^sub>1 \<subseteq> constant_rules C\<^sub>2"
  using assms unfolding constant_rules_def
  by(intro Un_mono,auto) (* also works with just auto, this is faster *)

lemma identity_rules_mono:
  assumes "C\<^sub>1 \<subseteq> C\<^sub>2"
  shows "identity_rules C\<^sub>1 \<subseteq> identity_rules C\<^sub>2"
   using assms unfolding identity_rules_def by auto

lemma standard_rules_mono:
  assumes "C\<^sub>1 \<subseteq> C\<^sub>2" "L\<^sub>1 \<subseteq> L\<^sub>2"
  shows "standard_rules C\<^sub>1 L\<^sub>1 \<subseteq> standard_rules C\<^sub>2 L\<^sub>2"
  using constant_rules_mono[OF assms(1)] identity_rules_mono[OF assms(2)] by auto

lemma maintainedA_invmono:
  assumes "C\<^sub>1 \<subseteq> C\<^sub>2" "L\<^sub>1 \<subseteq> L\<^sub>2"
  shows "maintainedA (standard_rules C\<^sub>2 L\<^sub>2) G \<Longrightarrow> maintainedA (standard_rules C\<^sub>1 L\<^sub>1) G"
  using standard_rules_mono[OF assms] by auto

lemma maintained_preserved_by_isomorphism:
  assumes "\<And> x. x \<in> vertices G \<Longrightarrow> (f \<circ> g) x = x" "graph G"
      and "maintained r (map_graph_fn G g)"
  shows "maintained r G"
proof(cases r)
  case (Pair L R)
  show ?thesis unfolding Pair proof(standard,goal_cases)
    case (1 h)
    from assms(3)[unfolded maintained_def Pair] is_graph_homomorphism_on_graph[OF this, of g]
    have "extensible (L, R) (map_graph_fn G g) (h O on_graph G g)" by auto
    then obtain h2
      where h2:"is_graph_homomorphism R (map_graph_fn G g) h2" "agree_on L (h O on_graph G g) h2"
      unfolding extensible_def by auto
    from 1 have h_id:"h O Id_on (vertices G) = h" unfolding is_graph_homomorphism_def by auto
    let ?h = "h2 O on_graph (map_graph_fn G g) f"
    from assms(1) have "on_graph G (f \<circ> g) = Id_on (vertices G)" by auto
    hence "map_graph_fn G (f \<circ> g) = G" using assms(2) map_graph_fn_id by auto
    with is_graph_homomorphism_on_graph[OF h2(1),of f]
    have igh:"is_graph_homomorphism R G ?h" by auto
    have "g x = g xa \<Longrightarrow> x \<in> (vertices G) \<Longrightarrow> xa \<in> (vertices G) \<Longrightarrow> x = xa" 
      for x xa using assms(1) o_def by metis
    hence "g x = g xa \<Longrightarrow> x \<in> (vertices G) \<Longrightarrow> xa \<in> (vertices G) \<Longrightarrow> (x, xa) \<in> Id_on (vertices G)"
      for x xa by auto
    hence id:"(on_graph G g) O on_graph (map_graph_fn G g) f = Id_on (vertices G)"
      using assms(1) by auto
    from agree_on_ext[OF h2(2),of "on_graph (map_graph_fn G g) f",unfolded O_assoc]
    have agh:"agree_on L h ?h" unfolding agree_on_def id h_id.
    from igh agh show ?case unfolding extensible_def by auto
  qed
qed

(* Slightly stronger version of Lemma 8:
   we reason about maintained rather than holds,
   and the quantification happens within the existential quantifier, rather than outside.
   A slight change is due to the type system of Isabelle:
     The existence of a type 'a large enough is assumed explicitly in the proof of Lemma 8.
     Here, it follows implicitly (and is explicitly constructed) via the type of standard' *)
lemma maintained_standard_noconstants:
  assumes mnt:"maintainedA (standard_rules C L) G'"
  and gr:"graph (G'::('V Standard_Constant, 'V') labeled_graph)"
         "fst ` edges G' \<subseteq> L" (* Graph on labels L *)
  and cf:"getRel S_Bot G' = {}" (* Conflict free *)
shows "\<exists> f g (G::('V, 'V') std_graph). G = map_graph_fn G (f o g) \<and> G = map_graph_fn G' f
              \<and> subgraph (map_graph_fn G g) G'
              \<and> standard' C G
              \<and> (\<forall> r. maintained r G' \<longrightarrow> maintained r G)"
proof -
  from mnt have "maintainedA (identity_rules L) G'" by auto
  from identity_rules[OF gr(1) this gr(2)] obtain h where
    h:"h \<circ> h = h" "ident_rel S_Idt (map_graph_fn G' h)" "subgraph (map_graph_fn G' h) G'" by blast
  have mg:"\<And> r. maintained r G' \<Longrightarrow> maintained r (map_graph_fn G' h)"
   using idemp_embedding_maintained_preserved[OF h(3)] h(1) by auto
  have mg_h : "graph (map_graph_fn G' h)" by auto
  from mnt have tr:"maintained (top_rule S_Top) G'" and ne:"maintained nonempty_rule G'" by auto
  from non_empty_rule_non_empty[OF ne gr(1)] obtain x where x:"x \<in> vertices G'" by blast
  from top_rule_full[OF tr gr(1)] x have top_nonempty:"(x, x) \<in> getRel S_Top G'" by metis
  have "\<And> c. c \<in> C \<Longrightarrow> \<exists>v. (v, v) \<in> getRel (S_Const c) (map_graph_fn G' h)" proof(goal_cases)
    case (1 c)
    with mnt have cr5: "maintained (const_exists c) G'"
              and cr7: "maintained (const_prop c) G'" unfolding constant_rules_def by blast+
    from top_nonempty cr5[unfolded maintained_holds_subset_iff[OF gr(1)]]
    obtain y z where yz:"(y,z) \<in> getRel (S_Const c) G'" by auto
    from this gr(1) have yzv:"y \<in> vertices G'" "z \<in> vertices G'" by (auto simp:getRel_def)
    from getRel_hom[OF yz yzv]
    have hi:"(h y,h z) \<in> getRel (S_Const c) (map_graph_fn G' h)".
    with h(2) cr7[THEN mg,unfolded maintained_holds_subset_iff[OF mg_h]] have "h y = h z" by force
    thus "\<exists> v. (v,v) \<in> getRel (S_Const c) (map_graph_fn G' h)" using hi by auto
  qed
  hence "\<forall> c. \<exists> v. c \<in> C \<longrightarrow> (v, v) \<in> getRel (S_Const c) (map_graph_fn G' h)" by blast
  from choice[OF this] obtain m
    where m:"\<And> x. x \<in> C \<Longrightarrow> (m x, m x) \<in> getRel (S_Const x) (map_graph_fn G' h)" by blast
  let ?m' = "\<lambda> x. if x \<in> m ` C then Inl (the_inv_into C m x) else Inr x"
  define f where "f \<equiv> ?m' o h"
  have "\<And> x y. x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> m x = m y \<Longrightarrow> x = y" proof(goal_cases)
    case (1 x y)
    with m have "(m x,m x) \<in> getRel (S_Const y) (map_graph_fn G' h)"
                "(m x,m x) \<in> getRel (S_Const x) (map_graph_fn G' h)" by metis+
    hence mx: "(m x,m x) \<in> getRel (S_Const y) G'"
              "(m x,m x) \<in> getRel (S_Const x) G'" using h(3) by force+
    from 1(1,2) mnt have cr8:"x \<noteq> y \<Longrightarrow> maintained (const_disj x y) G'"
      unfolding constant_rules_def by blast
    from cr8[unfolded maintained_holds_subset_iff[OF gr(1)],simplified] mx
    have "x\<noteq>y\<Longrightarrow>(m x,m x) \<in> :G':\<lbrakk>\<bottom>\<rbrakk>" by auto
    thus "x = y" using cf by auto
  qed
  hence "univalent (converse (BNF_Def.Gr C m))" unfolding univalent_def by auto
  hence inj_m:"inj_on m C" unfolding inj_on_def by auto

  from inj_on_the_inv_into[OF inj_m] have inj_m':"inj ?m'" unfolding inj_on_def by auto
  define G where "G = map_graph_fn G' f"
  hence G:"graph G" "f x \<in> vertices G" "getRel S_Bot G = {}" using x cf unfolding getRel_def
    by force+
  from comp_inj_on[OF inj_on_the_inv_into[OF inj_m] inj_Inl, unfolded o_def] inj_Inr
  have inj_m':"inj_on ?m' (vertices G')" unfolding inj_on_def by auto
  define g where "g = the_inv_into (vertices G') ?m'"

  have gf_h:"\<And> x. x \<in> vertices G' \<Longrightarrow> (g o f) x = h x" unfolding g_def f_def o_def
    apply(rule the_inv_into_f_f[OF inj_m']) using h unfolding subgraph_def graph_union_iff by auto

  have mg_eq:"map_graph_fn G' (g \<circ> f) = map_graph_fn G' h"
    by (rule map_graph_fn_eqI[OF gf_h])

  have "\<And> x. x \<in> vertices G' \<Longrightarrow> h x \<in> vertices G'" using h(3)
    unfolding subgraph_def graph_union_iff by(cases G',auto)
  hence gf_id:"\<And> x. x \<in> vertices G' \<Longrightarrow> (g o f) (h x) = (h x)"
    using h(1) gf_h unfolding o_def by metis
  { fix x assume "x \<in> vertices G"
    then obtain y where y:"f y = x" "y \<in> vertices G'" unfolding G_def by auto
    from gf_h[OF y(2)] have "(f o g) (f y) = f (h y)" unfolding o_def by auto
    also have "\<dots> = f y" using h(1) unfolding f_def o_def by metis
    finally have "(f o g) x = x" unfolding y.
  } note fg_id = this

  have fg_inv:"map_graph_fn G (f o g) = G"
    using h(1) G_def f_def mg_eq map_graph_fn_comp by (metis (no_types, lifting))

  have ir:"ident_rel S_Idt G" unfolding set_eq_iff proof(standard,standard,goal_cases)
    case (1 x)
    from this[unfolded G_def]
    obtain v1 v2 where v:"(v1,v2) \<in> getRel S_Idt G'" "x = (f v1,f v2)"
      unfolding getRel_def map_graph_def on_triple_def by auto
    hence vv:"v1 \<in> vertices G'" "v2 \<in> vertices G'" using gr unfolding getRel_def by auto
    with h(2) v(1) have "h v1 = h v2" unfolding image_def by blast
    hence x:"x = (f v1,f v1)" unfolding f_def v by auto
    from vv(1) show ?case unfolding x G_def by auto
  next
    case (2 x)
    hence x:"fst x = snd x" "fst x \<in> vertices G" by auto
    hence "(fst x) \<in> f ` vertices G'" unfolding G_def o_def by auto
    then obtain v where v:"v \<in> vertices G'" "f v = fst x" by auto
    hence hv:"h v \<in> vertices (map_graph_fn G' h)" by simp
    hence "(h v,h v) \<in> getRel S_Idt (map_graph_fn G' h)" unfolding h(2) by auto
    from getRel_hom[OF this hv hv]
    have "(?m' (h v),?m' (h v)) \<in> getRel S_Idt (map_graph_fn G' (?m' o h))"
      unfolding map_graph_fn_comp by fast
    hence "(f v,f v) \<in> getRel S_Idt (map_graph_fn G' f)" unfolding f_def by auto
    hence "(fst x,snd x) \<in> getRel S_Idt G" unfolding x v G_def by auto
    thus ?case unfolding G_def by auto
  qed

  from top_rule_full[OF tr gr(1)]
  have tr0:"getRel S_Top (map_graph_fn G' h)
          = {(x,y). x \<in> vertices (map_graph_fn G' h) \<and> y \<in> vertices (map_graph_fn G' h)}"
    and tr:"getRel S_Top G = {(x, y). x \<in> vertices G \<and> y \<in> vertices G}"
    unfolding G_def getRel_def on_triple_def map_graph_def by auto

  have m:"\<And> x. x \<in> C \<Longrightarrow> {(m x, m x)} = getRel (S_Const x) (map_graph_fn G' h)" proof fix x
    assume x:"x \<in> C"
    { fix y z assume a:"(y,z) \<in> getRel (S_Const x) (map_graph_fn G' h)"
      let ?t = "getRel S_Top (map_graph_fn G' h)"
      let ?r = "getRel (S_Const x) (map_graph_fn G' h)"
      have mx:"(m x,m x) \<in> getRel (S_Const x) (map_graph_fn G' h)" using m x by auto
      with a have v:"y \<in> vertices (map_graph_fn G' h)"
                    "z \<in> vertices (map_graph_fn G' h)"
                    "m x \<in> vertices (map_graph_fn G' h)" unfolding getRel_def by force+
      with tr0 have "(m x,y) \<in> ?t" "(z,m x) \<in> ?t" by auto
      with a mx have lhs:"(m x,z) \<in> ?r O ?t O ?r" "(y,m x) \<in> ?r O ?t O ?r" by auto
      from x mnt have "maintained (const_exists_rev x) G'"
                  and "maintained (const_prop x) G'" unfolding constant_rules_def by blast+
      hence cr6:"maintained (const_exists_rev x) (map_graph_fn G' h)"
        and cr7:"maintained (const_prop x) (map_graph_fn G' h)"
        by (intro mg, force)+
      hence "(m x,z) \<in> getRel S_Idt (map_graph_fn G' h)"
            "(y,m x) \<in> getRel S_Idt (map_graph_fn G' h)"
        using lhs unfolding maintained_holds_subset_iff[OF mg_h] by auto
      hence "y = m x" "z = m x" using h(2) by auto
    }
    thus "getRel (S_Const x) (map_graph_fn G' h) \<subseteq> {(m x, m x)}" by auto
  qed (insert m,auto)

  from mg_eq have mg_eq:"map_graph_fn G g = map_graph_fn G' h" unfolding G_def map_graph_fn_comp.

  { fix l fix v::"'V + 'V'"
    assume a:"(l, v)\<in>(\<lambda>c. (S_Const c, Inl c)) ` C"
    hence "getRel l G = {(v, v)}" using m proof(cases l)
      case (S_Const x) hence x:"l = S_Const x" "v = Inl x" "x \<in> C" using a by auto
      hence mx:"m x \<in> m ` C" by auto
      from m[OF x(3)] have "(m x,m x) \<in> getRel (S_Const x) (map_graph_fn G' h)" by auto
      hence "(S_Const x,m x,m x) \<in> edges (map_graph_fn G' h)" unfolding getRel_def by auto
      hence "m x \<in> vertices (map_graph_fn G' h)" unfolding map_graph_def Image_def by auto
      then obtain x' where x':"m x = h x'" "x' \<in> vertices G'" by auto
      from h(1) have hmx[simp]:"h (m x) = m x" unfolding x' o_def by metis
      hence fmx:"f (m x) = v" unfolding x f_def
        using the_inv_into_f_f[OF inj_m] inj_m[unfolded inj_on_def,rule_format,OF x(3)] mx by auto
      have "{(f (m x), f (m x))} = getRel l (map_graph_fn G (f \<circ> g))" 
        unfolding map_graph_fn_comp getRel_hom_map[OF map_graph_fn_graphI]
                  m[OF x(3),folded mg_eq x(1),symmetric] by auto
      hence gr:"getRel l G = {(f (m x), f (m x))}" unfolding fg_inv by blast
      show ?thesis unfolding gr fmx by (fact refl)
    qed auto
  } note cr = this

  have sg:"subgraph (map_graph_fn G g) G'" unfolding mg_eq using h(3).
  have std:"standard' C G" unfolding standard_def using G ir tr cr by blast
  have mtd:"\<And>r. maintained r G' \<Longrightarrow> maintained r G" proof(goal_cases)
    case (1 r) from mg[OF 1,folded mg_eq] maintained_preserved_by_isomorphism[OF fg_id G(1)]
    show ?case by metis
  qed
  
  show ?thesis using G_def fg_inv[symmetric] sg std mtd by blast
qed

end