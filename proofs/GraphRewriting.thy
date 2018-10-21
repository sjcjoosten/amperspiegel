theory GraphRewriting
  imports StandardRules
begin

(* Algorithm 1 on page 16 *)
text \<open>To describe Algorithm 1, we give a single step instead of the recursive call.
This allows us to reason about its effect without dealing with non-termination.
We define a worklist, saying what work can be done.
A valid selection needs to be made in order to ensure fairness.
To do a step, we define the function extend, and use it in make_step.
A function that always makes a valid selection is used in this step. \<close>

definition worklist :: "nat \<Rightarrow> ('a \<times> nat \<times> nat) set
           \<Rightarrow> (('a, 'b) labeled_graph \<times> ('a, 'b) labeled_graph) set
              \<Rightarrow> (nat \<times> ('a, 'b) labeled_graph \<times> ('a, 'b) labeled_graph \<times> ('b \<times> nat) set) set" where
"worklist n E Rs \<equiv> let G = LG E {0..<n} 
  in {(N,L,R,f). (L,R)\<in> Rs \<and> is_graph_homomorphism L G f \<and> N = Max (Range f)
                 \<and> \<not> extensible (L,R) G f }"

definition valid_selection where
"valid_selection Rs n E L R f \<equiv>
  let wl = worklist n E Rs in
    (Max (Range f), L,R,f) \<in> wl \<and>
    (\<forall> (N,_) \<in> wl. N \<ge> Max (Range f)) \<and>
    finite_graph R \<and>
    subgraph L R"

lemma valid_selection_exists:
  assumes "worklist n E Rs \<noteq> {}"
          "set_of_graph_rules Rs"
  shows "\<exists>L R f. valid_selection Rs n E L R f"
proof -
  define wl where "wl = worklist n E Rs" hence wl_ne:"wl \<noteq> {}" using assms(1) by auto
  let ?N = "LEAST N. N \<in> Domain wl"
  from wl_ne have "\<exists> N. N \<in> Domain wl" by auto
  with LeastI2 have "?N \<in> Domain wl" by metis
  then obtain L R f where NLRf:"(?N,L,R,f)\<in>wl" by auto
  hence N_def:"?N = Max (Range f)"
    and in_Rs: "(L,R) \<in> Rs" unfolding wl_def worklist_def Let_def by auto
  from Least_le wl_ne Domain.intros case_prodI2 
  have is_min:"(\<forall> (N',_) \<in> wl. N' \<ge> ?N)" by (metis (no_types, lifting))
  from in_Rs have "finite_graph R" "subgraph L R"
    using assms(2)[unfolded set_of_graph_rules_def] by auto
  with is_min NLRf N_def show ?thesis unfolding wl_def[symmetric] valid_selection_def by auto
qed

definition valid_selector where
"valid_selector Rs selector \<equiv> \<forall> n E.
   (worklist n E Rs \<noteq> {} \<longrightarrow> (\<exists> (L,R,f)\<in>UNIV. selector n E = Some (L,R,f)
                               \<and> valid_selection Rs n E L R f)) \<and>
   (worklist n E Rs = {} \<longrightarrow> selector n E = None)"

lemma valid_selectorD[dest]:
  assumes "valid_selector Rs selector"
  shows "worklist n E Rs = {} \<longleftrightarrow> selector n E = None"
        "selector n E = Some (L,R,f) \<Longrightarrow> valid_selection Rs n E L R f"
  using assms[unfolded valid_selector_def,rule_format,of n E]
  by (cases "worklist n E Rs = {}",auto)

(* just to show the existence of a valid selector *)
definition non_constructive_selector where
"non_constructive_selector Rs n E \<equiv> let wl = worklist n E Rs in
   if wl = {} then None else Some (SOME (L,R,f). valid_selection Rs n E L R f) "

lemma non_constructive_selector:
  assumes "set_of_graph_rules Rs"
  shows "valid_selector Rs (non_constructive_selector Rs)"
  unfolding valid_selector_def proof((clarify,standard;clarify),goal_cases)
  case (1 n E)
  let ?x = "(SOME (L, R, f). valid_selection Rs n E L R f)"
  from valid_selection_exists[OF 1 assms]
  have "\<exists> L R f. valid_selection Rs n E L R f".
  hence "\<exists> x. valid_selection Rs n E (fst x) (fst (snd x)) (snd (snd x))"
    by auto
  from this prod.case_eq_if tfl_some
  have "\<not> valid_selection Rs n E (fst ?x) (fst (snd ?x)) (snd (snd ?x)) \<Longrightarrow> False"
    by (metis (mono_tags, lifting))
  thus ?case unfolding non_constructive_selector_def Let_def using 1 by (auto simp:prod_eq_iff)
qed (auto simp:non_constructive_selector_def)

definition extend ::
    "nat \<Rightarrow> ('b, 'a::linorder) labeled_graph
         \<Rightarrow> ('c, 'a) labeled_graph \<Rightarrow> ('a \<times> nat) set \<Rightarrow> ('a \<times> nat) set" where
"extend n L R f \<equiv> f \<union> 
   (let V_new = sorted_list_of_set (vertices R - vertices L)
    in set (zip V_new [n..<(n+length V_new)]))"

definition nextMax :: "nat set \<Rightarrow> nat"
  where
  "nextMax x \<equiv> if x = {} then 0 else Suc (Max x)"

lemma list_sorted_max[simp]: (* TODO: move *)
  shows "sorted list \<Longrightarrow> list = (x#xs) \<Longrightarrow> fold max xs x = (last list)"
proof (induct list arbitrary:x xs)
  case (Cons a list)
  hence "xs = y # ys \<Longrightarrow> fold max ys y = last xs" "sorted (x # xs)" "sorted xs" for y ys 
    using Cons.prems(1,2) by auto
  hence "xs \<noteq> [] \<Longrightarrow> fold max xs x = last xs"
    by (metis (full_types) fold_simps(2) max.orderE sorted.elims(2) sorted2)
  thus ?case unfolding Cons by auto
qed auto

lemma nextMax_set[simp]:
  assumes "sorted xs"
  shows "nextMax (set xs) = (if xs = Nil then 0 else Suc (last xs))"
  using assms
proof(induct xs)
  case Nil show ?case unfolding nextMax_def by auto
next
  case (Cons a list)
  hence "list \<noteq> [] \<Longrightarrow> fold max list a = last list"
    using list_sorted_max by (metis last.simps)
  thus ?case unfolding nextMax_def Max.set_eq_fold by auto
qed

lemma nextMax_Un_eq[simp]:
"finite x \<Longrightarrow> finite y \<Longrightarrow> nextMax (x \<union> y) = max (nextMax x) (nextMax y)"
  unfolding nextMax_def using Max_Un by auto

lemma extend: (* extensible into the new graph *)
  assumes "is_graph_homomorphism L (LG E {0..<n}) f" "graph_rule (L,R)"
  defines "g \<equiv> extend n L R f"
  defines "G' \<equiv> LG ((on_triple g `` (edges R)) \<union> E) {0..<max n (nextMax (Range g))}"
  shows "is_graph_homomorphism R G' g" "f \<subseteq> g" "subgraph (LG E {0..<n}) G'"
        "weak_universal (L, R) (LG E {0..<n}) G' f g"
proof -
  have [intro!]:"finite (Range (set x))" for x by(induct x,auto)
  from assms have fin_R_L[simp]:"finite (vertices R - vertices L)"
    and gr_R:"graph R" by auto
  from assms have f_dom:"Domain f = vertices L"
    and f_uni:"univalent f" unfolding is_graph_homomorphism_def by auto
  from assms[unfolded is_graph_homomorphism_def]
  have "f `` vertices L \<subseteq> vertices (LG E {0..<n})" by blast
  hence f_ran:"Range f \<subseteq> {0..<n}" using f_dom by auto
  let ?g = "(let V_new = sorted_list_of_set (vertices R - vertices L)
              in set (zip V_new [n..<n + length V_new]))" (* new part of g *)
  have fin_g':"finite ?g" "finite (Range ?g)" unfolding Let_def by auto
  have "finite (vertices R)" "finite (vertices L)" and subsLR: "vertices L \<subseteq> vertices R"
    using assms(2) finite_subset unfolding subgraph_def graph_union_iff by auto
  hence "finite (Domain f)" "univalent f" using assms(1)
    unfolding is_graph_homomorphism_def by auto
  hence fin_f:"finite (Range f)" unfolding Range_snd by auto
  hence fin_g:"finite (Range g)" unfolding extend_def g_def Let_def Range_Un_eq by auto
  have nextMax_f:"nextMax (Range f) \<le> n"
    using f_ran Max_in[OF fin_f] by (simp add:nextMax_def Suc_leI subset_eq)

  have "x \<in> Domain ?g \<Longrightarrow> x \<notin> Domain f" for x unfolding f_dom Let_def by auto
  hence g_not_f:"(x,y) \<in> ?g \<Longrightarrow> (x,z) \<notin> f" for x y z by auto
  have uni_g':"univalent ?g" "univalent (converse ?g)" unfolding Let_def by auto
  with f_uni have uni_g:"univalent g" by (auto simp:g_def extend_def g_not_f)
  from fin_g have "(a,b) \<in> g \<Longrightarrow> b < Suc (Max (Range g))" for a b
    unfolding less_Suc_eq_le by (rule Max.coboundedI) force
  hence "(a,b) \<in> g \<Longrightarrow> b < nextMax (Range g)" for a b
    unfolding nextMax_def by (cases "Range g = {}",auto)
  hence in_g:"(a,b) \<in> g \<Longrightarrow> b < max n (nextMax (Range g))" for a b by fastforce
  let ?G = "LG E {0..<n}"
  have gr_G:"graph ?G" using assms(1) unfolding is_graph_homomorphism_def by blast
  hence "(a, aa, b) \<in> E \<Longrightarrow> b < max n c" "(a, aa, b) \<in> E \<Longrightarrow> aa < max n c"
    for a aa b c by fastforce+
  hence gr_G':"graph G'" unfolding G'_def using in_g by auto
  show "subgraph (LG E {0..<n}) G'"
    unfolding subgraph_def2[OF gr_G gr_G'] unfolding G'_def by auto
  have g_dom:"vertices R = Domain g" using subsLR
    unfolding g_def extend_def Domain_Un_eq f_dom by (auto simp:Let_def)
  show "is_graph_homomorphism R G' g"
    by (intro is_graph_homomorphismI[OF g_dom _ uni_g _ gr_R gr_G'])
       (auto simp:G'_def intro:in_g)
  have ln:"length x = length [n..<n + length x]" for x by auto
  show "f \<subseteq> g" by (auto simp:g_def extend_def)
  have "max n (nextMax (Range ?g)) = n + length (sorted_list_of_set (vertices R - vertices L))"
    unfolding Let_def Range_snd set_map[symmetric] map_snd_zip[OF ln] nextMax_set[OF sorted_upt]
    by fastforce
  hence n_eq:"n + length (sorted_list_of_set (vertices R - vertices L)) = max n (nextMax (Range g))"
    unfolding Range_snd[symmetric] g_def extend_def Range_Un_eq
              nextMax_Un_eq[OF fin_f fin_g'(2)] max.assoc[symmetric] max_absorb1[OF nextMax_f]
    by auto
  show "weak_universal (L, R) ?G G' f g" proof fix a:: "('b \<times> nat) set" fix b G
    assume a:"is_graph_homomorphism (snd (L, R)) G a"
             "is_graph_homomorphism ?G G b" "f O b \<subseteq> a"
    hence univ_b:"univalent b" and univ_a:"univalent a"
      and rng_b:"Range b \<subseteq> vertices G" and rng_a:"Range a \<subseteq> vertices G"
      and ep_b:"edge_preserving b (edges (LG E {0..<n})) (edges G)"
      and ep_a:"edge_preserving a (edges R) (edges G)"
      unfolding is_graph_homomorphism_def prod.sel labeled_graph.sel by blast+
    from a have dom_b:"Domain b = {0..<n}"
      and dom_a:"Domain a = vertices R" and v6: "graph G"
      unfolding is_graph_homomorphism_def prod.sel labeled_graph.sel by auto

    have help_dom_b:"(y, z) \<in> b \<Longrightarrow> n \<le> y \<Longrightarrow> False" for y z using dom_b
      by (metis Domain.DomainI atLeastLessThan_iff not_less)
    have disj_doms:"Domain b \<inter> Domain (?g\<inverse> O a) = {}" using help_dom_b
      unfolding Let_def by (auto dest!:set_zip_leftD)

    let ?h = "b \<union> ?g\<inverse> O a"
    have "g O ?h = f O b \<union> ?g O b \<union> ((f O ?g\<inverse>) O a \<union> (?g O ?g\<inverse>) O a)"
      unfolding g_def extend_def by blast
    also have "f O b \<subseteq> a" by (fact a(3))
    also have "(?g O ?g\<inverse>) = Id_on (vertices R - vertices L)"
      unfolding univalent_O_converse[OF uni_g'(2)] unfolding Let_def by auto
    also have "(f O ?g\<inverse>) = {}" using f_ran unfolding Let_def by (auto dest!:set_zip_leftD)
    also have "?g O b = {}" using help_dom_b unfolding Let_def by (auto dest!:set_zip_rightD)
    finally have gOh:"g O ?h \<subseteq> a" by blast

    have dg:"Domain (?g\<inverse>) = {n..<max n (nextMax (Range g))}"
      unfolding Let_def Domain_converse Range_set_zip[OF ln] atLeastLessThan_upt
      unfolding Range_snd n_eq ..
    have "?g `` Domain a = ?g `` ((vertices R - vertices L) \<union> vertices L)"
      using dom_a subsLR by auto
    also have "\<dots> = ?g `` (vertices R - vertices L) \<union> ?g `` vertices L" by auto
    also have "?g `` vertices L = {}" apply(rule Image_outside_Domain)
      unfolding Let_def Domain_set_zip[OF ln] by auto
    also have "?g `` (vertices R - vertices L) = Range ?g"
      apply(rule Image_is_Domain)
      unfolding Let_def Domain_set_zip[OF ln] by auto
    also have "Range ?g = {n..<max n (nextMax (Range g))}"
      unfolding Let_def Range_set_zip[OF ln] set_sorted_list_of_set[OF fin_R_L] 
      unfolding n_eq set_upt..
    finally have dg2:"?g `` Domain a = {n..<max n (nextMax (Range g))}" by auto
    have "Domain (?g\<inverse> O a) = {n..<max n (nextMax (Range g))}"
      unfolding Domain_id_on converse_converse dg dg2 by auto
    hence v1: "vertices G' = Domain ?h" unfolding G'_def Domain_Un_eq dom_b by auto
    have "b `` vertices G' \<subseteq> vertices G" "(?g\<inverse> O a) `` vertices G' \<subseteq> vertices G"
      using rng_a rng_b by auto
    hence v2: "?h `` vertices G' \<subseteq> vertices G" by blast
    have v3: "univalent ?h"
      using disj_doms univalent_union[OF univ_b univalent_composes[OF uni_g'(2) univ_a]] by blast
    (* showing edge preservation *)
    { fix l x y x' y' assume a2:"(l,x,y) \<in> edges G'" "(x,x') \<in> ?h" "(y,y') \<in> ?h"
      have "(l,x',y') \<in> edges G" proof(cases "(l,x,y) \<in> edges ?G")
        case True
        with gr_G[THEN restrictD]
        have "x \<in> Domain b" "y \<in> Domain b" unfolding dom_b by auto
        hence "x \<notin> Domain (converse ?g O a)" "y \<notin> Domain (converse ?g O a)"
          using disj_doms by blast+
        hence "(x,x') \<in> b" "(y,y') \<in> b" using a2 by auto
        with ep_b True show ?thesis unfolding edge_preserving by auto
      next
        case False
        hence "(l,x,y) \<in> on_triple g `` edges R" using a2(1) unfolding G'_def by auto
        then obtain r_x r_y
          where r:"(l,r_x,r_y) \<in> edges R" "(r_x,x) \<in> g" "(r_y,y) \<in> g" by auto
        hence "(r_x,x') \<in> a" "(r_y,y') \<in> a"
          using gOh a2(2,3) by auto
        hence "(l,x',y') \<in> on_triple a `` edges R" using r(1) unfolding on_triple_def by auto
        thus ?thesis using ep_a unfolding edge_preserving by auto
      qed
    }
    hence v4: "edge_preserving ?h (edges G') (edges G)" by auto
    have "is_graph_homomorphism G' G ?h" by(fact is_graph_homomorphismI[OF v1 v2 v3 v4 gr_G' v6])
    thus "\<exists>h. is_graph_homomorphism G' G h \<and> b \<subseteq> h" by auto
  qed
qed

lemma selector_pushout:
  assumes "valid_selector Rs selector" "Some (L,R,f) = selector n E"
  defines "G \<equiv> (LG E {0..<n})"
  assumes "graph G"
  defines "g \<equiv> extend n L R f"
  defines "G' \<equiv> LG (on_triple g `` edges R \<union> E) {0..<max n (nextMax (Range g))}"
  shows "pushout_step (L,R) G G'"
proof -
  have "valid_selection Rs n E L R f"
    using assms by(cases "selector n E",auto)
  hence igh:"is_graph_homomorphism L G f" "graph_rule (L, R)"
    unfolding valid_selection_def worklist_def G_def Let_def by auto
  have "subgraph G G'"
       "is_graph_homomorphism (fst (L, R)) G f"
       "is_graph_homomorphism (snd (L, R)) G' g"
       "f \<subseteq> g"
       "weak_universal (L, R) G G' f g"
    using extend[OF igh[unfolded G_def],folded g_def,folded G'_def,folded G_def] igh(1)
    by auto
  thus ?thesis unfolding pushout_step_def by auto
qed

(* Make step does a single step in the algorithm.
   It needs a valid_selector as first argument. *)
definition make_step where
"make_step selector n E \<equiv>
   case selector n E of
     None \<Rightarrow> (n,E) |
     Some (L,R,f) \<Rightarrow> (let g = extend n L R f in
         (max n (Suc (Max (Range g))), (on_triple g `` (edges R)) \<union> E))"


(* Work towards Lemma 9. Give a variation on Algorithm 1 where we do n iterations.
We show that the sequence of doing n iterations is itself a (simple) weak pushout chain.
*)

(* Create 'master theorem' relating 'holds' and 'entails' to the outcome *)
end
