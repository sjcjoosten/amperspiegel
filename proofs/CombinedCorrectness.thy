theory CombinedCorrectness
  imports GraphRewriting StandardRules
begin
(* TODO: Create 'master theorem' relating 'holds' and 'entails' to the outcome. *)
thm lcg_through_make_step maintained_standard_noconstants
    consequence_graphD maintained_holds_iff least_consequence_graph_def least_def

(* a somewhat concrete function to get the model if one exists *)
definition the_model where
"the_model C Rs
  \<equiv> let L = fst ` UNION Rs (edges o snd);
        Rules = Rs \<union> (standard_rules C L);
        sel = non_constructive_selector Rules 
     in the_lcg sel Rules (0,{})"

abbreviation check_consistency where
  "check_consistency C Rs \<equiv> getRel S_Bot (the_model C Rs) = {}"

definition transl_rules where
  "transl_rules T = UNION T (\<lambda> (x,y). {(translation x, translation (A_Int x y)),(translation y, translation (A_Int y x))})"

lemma gr_transl_rules:
  "x \<in> transl_rules T \<Longrightarrow> graph_rule x"
  using graph_rule_translation unfolding transl_rules_def by blast

lemma check_consistency:
  assumes "finite T" "finite C"
  shows "check_consistency C (transl_rules T) \<longleftrightarrow> consistent TYPE(nat) C T"
   (is "?lhs = ?rhs")
proof -
  from assms(1) have fin_t:"finite (transl_rules T)" unfolding transl_rules_def by fast
  define L where "L = fst ` UNION (transl_rules T) (edges \<circ> snd)"
  have "finite (UNION (transl_rules T) (edges \<circ> snd))" using fin_t gr_transl_rules by auto
  hence fin_l:"finite L" unfolding L_def by auto
  define Rules where "Rules = transl_rules T \<union> standard_rules C L"
  hence fin_r:"finite Rules" using assms(2) fin_t fin_l by auto
  have "\<forall>R\<in>transl_rules T. graph_rule R" using gr_transl_rules by blast
  moreover have "\<forall>R\<in> constant_rules C. graph_rule R" using constant_rules_graph_rule by auto
  moreover have "\<forall>R\<in> identity_rules L. graph_rule R" using identity_rules_graph_rule by auto
  moreover have "\<forall>R\<in> {top_rule S_Top,nonempty_rule}. graph_rule R" using are_rules(1,2) by fastforce
  ultimately have gr:"set_of_graph_rules Rules" unfolding set_of_graph_rules_def Rules_def ball_Un
    by blast
  define sel where "sel = non_constructive_selector Rules"
  hence sel:"valid_selector Rules sel" using gr non_constructive_selector by auto
  define cfg where "cfg = the_lcg sel Rules (0, {})"
  have cfg:"cfg = the_model C (transl_rules T)"
    unfolding cfg_def sel_def Rules_def L_def the_model_def Let_def..
  have cfg_c:"least_consequence_graph TYPE('a + nat) Rules (graph_of (0,{})) cfg"
    unfolding cfg_def
    by (rule lcg_through_make_step[OF fin_r gr _ sel],auto)
  hence cfg_sdt:"maintainedA (standard_rules C L) cfg"
    and cfg_g: "graph cfg"
    and cfg_l:"least TYPE('a + nat) Rules (graph_of (0, {})) cfg"
    and cfg_m:"r \<in> transl_rules T \<Longrightarrow> maintained r cfg" for r
    unfolding Rules_def least_consequence_graph_def by auto
  have cfg_lbl:"fst ` edges cfg \<subseteq> L" sorry
  have d1: "?lhs \<Longrightarrow> ?rhs" proof -
    assume ?lhs
    from maintained_standard_noconstants[OF cfg_sdt cfg_g cfg_lbl this[folded cfg]]
    obtain G :: "('a Standard_Constant, 'a + nat) labeled_graph"
      where G_std:"standard' C G"
      and m:"maintained r cfg \<Longrightarrow> maintained r G"
      for r :: "('a Standard_Constant, nat) Graph_PreRule"
      by blast
    hence g:"graph G" unfolding standard_def by auto
    have "(a,b)\<in>T \<Longrightarrow> G \<tturnstile> (a,b)" for a b apply(subst eq_as_subsets)
      using cfg_m[unfolded transl_rules_def,THEN m] maintained_holds_iff[OF g] by blast
    hence h:"(\<forall>S\<in>T. G \<tturnstile> S)" by auto
    with G_std show ?rhs unfolding model_def by blast
  qed
  have d2: "\<not> ?lhs \<Longrightarrow> ?rhs \<Longrightarrow> False" proof -
    assume "\<not> ?lhs"
    then obtain a b where ab:"(S_Bot,a,b) \<in> edges cfg"
      "a \<in> vertices cfg" "b \<in> vertices cfg"
      using cfg_g unfolding cfg getRel_def by auto
    assume ?rhs then obtain G :: "('a Standard_Constant, 'a + nat) labeled_graph"
      where G:"model C G T" by auto
    with model_def have std:"standard' C G" and holds:"\<forall>S\<in>T. G \<tturnstile> S" by fast+
    hence g:"graph G" unfolding standard_def by auto
    from std have std_maintained:"maintainedA (standard_rules C L) G" sorry
    from maintained_holds_iff[OF g] holds
    have "maintainedA (transl_rules T) G" unfolding transl_rules_def by auto
    hence mnt:"maintainedA Rules G" unfolding Rules_def using std_maintained by auto
    from consequence_graphI[OF _ _ g] gr[unfolded set_of_graph_rules_def] mnt
    have cg:"consequence_graph Rules G" by fast
    with cfg_l[unfolded least_def]
    have mtd:"maintained (graph_of (0, {}), cfg) G" by blast
    have "is_graph_homomorphism (fst (graph_of (0::nat, {}), cfg)) G {}"
      unfolding is_graph_homomorphism_def using g by auto
    with mtd maintained_def have "extensible (graph_of (0, {}), cfg) G {}" by auto
    then obtain g where "edges (map_graph g cfg) \<subseteq> edges G" "vertices cfg = Domain g"
      unfolding extensible_def is_graph_homomorphism_def2 graph_union_iff by auto
    hence "\<exists> a b. (S_Bot,a,b) \<in> edges G" using ab unfolding edge_preserving by auto
    thus False using std unfolding standard_def getRel_def by auto
  qed
  from d1 d2 show ?thesis by auto
qed

(* prove the model for the consistency-problem algorithm
   is a model iff one exists *)

(* define the entailment-problem algorithm
   given a finite set of graph-rules
   using the consistency-problem algorithm *)

find_theorems entails

(* prove the model for the entailment-problem algorithm
   gives the correct answer *)

(* show that in the case of conflict, we can abort the consistency-problem algorithm after some n *)


end