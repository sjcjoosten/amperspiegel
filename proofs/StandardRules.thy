theory StandardRules
imports StandardModels RuleSemanticsConnection
begin

(* Remark at Definition 16*)
lemma conflict_free:
":G:\<lbrakk>A_Lbl l\<rbrakk> = {} \<longleftrightarrow> (\<forall> (l',x,y)\<in>edges G. l' \<noteq> l)"
  by (auto simp:getRel_def)

(* Definition 17 *)
definition top_rule :: "'l \<Rightarrow> ('l,nat) Graph_PreRule" where	
"top_rule t = (LG {} {0,1},LG {(t,0,1)} {0,1})"	
 definition nonempty_rule :: "('l,nat) Graph_PreRule" where	
"nonempty_rule = (LG {} {},LG {} {0})"	
 (* gets a reflexive relation-label as argument *)	
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

(* Remark just before Lemma 7: if I is an identity, it maintains the identity rules *)
lemma ident_rel_refl:
  assumes "graph G" "ident_rel idt G"
  shows "maintained (reflexivity_rule idt) G"
  unfolding reflexivity_rule_def
proof(rule maintainedI) fix f
  assume "is_graph_homomorphism (LG {} {0}) G f"
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
  using assms by fastforce+

definition identity_rules ::
  "'a Standard_Constant set \<Rightarrow> (('a Standard_Constant, nat) Graph_PreRule) set" where
  "identity_rules L \<equiv> {reflexivity_rule S_Idt,transitive_rule S_Idt,symmetry_rule S_Idt}
                       \<union> congruence_rules S_Idt L"

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
(* BNF_Def.Gr *)
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

(* Work towards Lemma 8 *)

end