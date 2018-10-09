theory LabeledGraphSemantics
imports LabeledGraphs
begin

definition getRel where
"getRel l G = {(x,y). (l,x,y) \<in> edges G}"

lemma getRel_subgraph[simp]:
  assumes "(y, z) \<in> getRel l G" "subgraph G G'"
  shows "(y,z) \<in> getRel l G'" using assms by (auto simp:getRel_def subgraph_def graph_union_iff)

lemma getRel_homR: (* slows down proofs in the common case *)
  assumes "(y, z) \<in> getRel l G" "(y,u) \<in> f" "(z,v) \<in> f"
  shows "(u, v) \<in> getRel l (map_graph f G)"
  using assms by (auto simp:getRel_def on_triple_def)

lemma getRel_hom[intro]: (* faster proofs in the common case *)
  assumes "(y, z) \<in> getRel l G" "y \<in> vertices G" "z \<in> vertices G"
  shows "(f y, f z) \<in> getRel l (map_graph_fn G f)"
  using assms by (auto intro!:getRel_homR)

lemma getRel_hom_map[simp]: (* two-way proofs *)
  assumes "graph G"
  shows "getRel l (map_graph_fn G f) = map_prod f f ` (getRel l G)"
proof
  { fix x y
    assume a:"(x, y) \<in> getRel l G"
    hence "x \<in> vertices G" "y\<in> vertices G" using assms unfolding getRel_def by auto
    hence "(f x, f y) \<in> getRel l (map_graph_fn G f)" using a by auto
  }
  then show "map_prod f f ` getRel l G \<subseteq> getRel l (map_graph_fn G f)" by auto
qed (cases G,auto simp:getRel_def)

(* Deviating from the paper in having a constant constructor.
   We'll use that constructor for top, bottom, etc.. *)
datatype 'v allegorical_term
 = A_Int "'v allegorical_term" "'v allegorical_term"
 | A_Cmp "'v allegorical_term" "'v allegorical_term"
 | A_Cnv "'v allegorical_term"
 | A_Lbl (a_lbl : 'v)

fun semantics where
"semantics G (A_Int a b) = semantics G a \<inter> semantics G b" |
"semantics G (A_Cmp a b) = semantics G a O semantics G b" |
"semantics G (A_Cnv a) = converse (semantics G a)" |
"semantics G (A_Lbl l) = getRel l G"

notation semantics (":_:\<lbrakk>_\<rbrakk>" 55)

type_synonym 'v sentence = "'v allegorical_term \<times> 'v allegorical_term"

datatype 'v Standard_Constant = S_Top | S_Bot | S_Idt | S_Const 'v

abbreviation holds where
"holds G S \<equiv> :G:\<lbrakk>fst S\<rbrakk> = :G:\<lbrakk>snd S\<rbrakk>"
notation holds (infix "\<tturnstile>" 55)

abbreviation subset_sentence where
"subset_sentence A B \<equiv> (A,A_Int A B)"

notation subset_sentence (infix "\<sqsubseteq>" 60)

lemma sentence_iff[simp]: (* Lemma 1 *)
  "G \<tturnstile> e\<^sub>1 \<sqsubseteq> e\<^sub>2 = (:G:\<lbrakk>e\<^sub>1\<rbrakk> \<subseteq> :G:\<lbrakk>e\<^sub>2\<rbrakk>)" and
  eq_as_subsets:
  "G \<tturnstile> (e\<^sub>1, e\<^sub>2) = (G \<tturnstile> e\<^sub>1 \<sqsubseteq> e\<^sub>2 \<and> G \<tturnstile> e\<^sub>2 \<sqsubseteq> e\<^sub>1)"
  by auto

lemma getRel_map_fn[intro]:
  assumes "a2 \<in> vertices G" "b2 \<in> vertices G" "(a2,b2) \<in> getRel l G"
          "f a2 = a" "f b2 = b"
        shows "(a,b) \<in> getRel l (map_graph_fn G f)"
proof -
  from assms(1,2)
  have "((l, a2, b2), (l, f a2, f b2)) \<in> on_triple {(a, f a) |a. a \<in> vertices G}" by auto
  thus ?thesis using assms(3-) by (simp add:getRel_def BNF_Def.Gr_def Image_def,blast)
qed
  

end