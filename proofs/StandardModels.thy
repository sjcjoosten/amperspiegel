theory StandardModels
imports LabeledGraphSemantics
begin

abbreviation "a_bot \<equiv> A_Lbl S_Bot"
abbreviation "a_top \<equiv> A_Lbl S_Top"
abbreviation "a_idt \<equiv> A_Lbl S_Idt"
notation a_bot ("\<bottom>")
notation a_top ("\<top>")
notation a_idt ("\<one>")
                                       
type_synonym 'v std_term = "'v Standard_Constant allegorical_term"
type_synonym 'v std_sentence = "'v std_term \<times> 'v std_term"
type_synonym 'v std_graph = "('v Standard_Constant, 'v Standard_Constant) labeled_graph"

abbreviation ident_rel where
"ident_rel idt G \<equiv> getRel idt G = (\<lambda> x.(x,x)) ` vertices G"

lemma ident_relI[intro]:
  assumes min:"\<And> x. x \<in> vertices G \<Longrightarrow> (x,x) \<in> getRel idt G"
  and max1:"\<And> x y. (x,y) \<in> getRel idt G \<Longrightarrow> x = y"
  and max2:"\<And> x y. (x,y) \<in> getRel idt G \<Longrightarrow> x \<in> vertices G"
shows "ident_rel idt G"
proof
  from max1 max2 have "\<And> x y. (x,y) \<in> getRel idt G \<Longrightarrow> (x = y \<and> x \<in> vertices G)" by simp
  thus "getRel idt G \<subseteq> (\<lambda>x. (x, x)) ` vertices G" by auto
  show "(\<lambda>x. (x, x)) ` vertices G \<subseteq> getRel idt G" using min by auto
qed

definition standard :: "'l set \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('l, 'l) labeled_graph \<Rightarrow> bool" where
"standard C b t idt G
   \<equiv> G = restrict G
   \<and> vertices G \<noteq> {}
   \<and> ident_rel idt G
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