theory LabeledGraphSemantics
imports LabeledGraphs
begin

definition getRel where
"getRel l G = {(x,y). (l,x,y) \<in> edges G}"

(* Deviating from the paper in having a constant constructor.
   We'll use that constructor for top, bottom, etc.. *)
datatype 'v allegorical_term
 = A_Int "'v allegorical_term" "'v allegorical_term"
 | A_Cmp "'v allegorical_term" "'v allegorical_term"
 | A_Cnv "'v allegorical_term"
 | A_Lbl 'v

datatype 'v Standard_Constant = S_Top | S_Bot | S_Idt | S_Const 'v

abbreviation "a_bot \<equiv> A_Lbl S_Bot"
abbreviation "a_top \<equiv> A_Lbl S_Top"
notation a_bot ("\<bottom>")
notation a_top ("\<top>")

fun semantics where
"semantics G (A_Int a b) = semantics G a \<inter> semantics G b" |
"semantics G (A_Cmp a b) = semantics G a O semantics G b" |
"semantics G (A_Cnv a) = converse (semantics G a)" |
"semantics G (A_Lbl l) = getRel l G"

notation semantics (":_:\<lbrakk>_\<rbrakk>" 55)

type_synonym 'v sentence = "'v allegorical_term \<times> 'v allegorical_term"
type_synonym 'v std_term = "'v Standard_Constant allegorical_term"
type_synonym 'v std_sentence = "'v std_term \<times> 'v std_term"
type_synonym 'v std_graph = "('v Standard_Constant, 'v Standard_Constant) labeled_graph"

abbreviation holds where
"holds G S \<equiv> :G:\<lbrakk>fst S\<rbrakk> = :G:\<lbrakk>snd S\<rbrakk>"
notation holds (infix "\<tturnstile>" 55)

abbreviation subset_sentence where
"subset_sentence A B \<equiv> (A,A_Int A B)"

notation subset_sentence (infix "\<sqsubseteq>" 60)

lemma sentence_iff: (* Lemma 1 *)
  "G \<tturnstile> e\<^sub>1 \<sqsubseteq> e\<^sub>2 = (:G:\<lbrakk>e\<^sub>1\<rbrakk> \<subseteq> :G:\<lbrakk>e\<^sub>2\<rbrakk>)"
  "G \<tturnstile> (e\<^sub>1, e\<^sub>2) = (G \<tturnstile> e\<^sub>1 \<sqsubseteq> e\<^sub>2 \<and> G \<tturnstile> e\<^sub>2 \<sqsubseteq> e\<^sub>1)"
  by auto

definition standard :: "'l set \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('l, 'l) labeled_graph \<Rightarrow> bool" where
"standard C b t idt G
   \<equiv> G = restrict G
   \<and> vertices G \<noteq> {}
   \<and> getRel idt G = {(x,x). x\<in>vertices G}
   \<and> getRel b G = {}
   \<and> getRel t G = {(x,y). x\<in>vertices G \<and> y\<in>vertices G}
   \<and> (\<forall> c \<in> C. getRel c G = {(c,c)})"

abbreviation standard' :: "'a std_graph \<Rightarrow> bool" where
"standard' \<equiv> standard (S_Const ` UNIV) S_Bot S_Top S_Idt"

definition model :: "'a std_graph \<Rightarrow> ('a std_sentence) set \<Rightarrow> bool" where
"model G T \<equiv> standard' G \<and> (\<forall> S \<in> T. G \<tturnstile> S)"
notation model (infix "\<tturnstile>\<^sub>S" 55) (* S for standard *)

abbreviation consistent :: "('a std_sentence) set \<Rightarrow> bool" where
"consistent T \<equiv> \<exists> G. model G T"

definition entails where
"entails T S \<equiv> \<forall> G. G \<tturnstile>\<^sub>S T \<longrightarrow> G \<tturnstile> S"

lemma standard_top_not_bot[intro]:
"standard' G \<Longrightarrow> :G:\<lbrakk>\<bottom>\<rbrakk> \<noteq> :G:\<lbrakk>\<top>\<rbrakk>"
  unfolding standard_def by auto

lemma consistent_iff_entails_nonsense: (* Lemma 2 *)
"consistent T = (\<not> entails T (\<bottom>,\<top>))"
proof
  show "consistent T \<Longrightarrow> \<not> entails T (\<bottom>, \<top>)"
    using standard_top_not_bot unfolding entails_def model_def
    by fastforce
qed (auto simp:entails_def model_def)

end