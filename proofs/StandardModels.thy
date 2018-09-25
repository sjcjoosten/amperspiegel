theory StandardModels
imports LabeledGraphSemantics
begin

abbreviation "a_bot \<equiv> A_Lbl S_Bot"
abbreviation "a_top \<equiv> A_Lbl S_Top"
notation a_bot ("\<bottom>")
notation a_top ("\<top>")

type_synonym 'v std_term = "'v Standard_Constant allegorical_term"
type_synonym 'v std_sentence = "'v std_term \<times> 'v std_term"
type_synonym 'v std_graph = "('v Standard_Constant, 'v Standard_Constant) labeled_graph"

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