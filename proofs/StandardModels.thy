theory StandardModels
imports LabeledGraphSemantics Main
begin

abbreviation "a_bot \<equiv> A_Lbl S_Bot"
abbreviation "a_top \<equiv> A_Lbl S_Top"
abbreviation "a_idt \<equiv> A_Lbl S_Idt"
notation a_bot ("\<bottom>")
notation a_top ("\<top>")
notation a_idt ("\<one>")
                                       
type_synonym 'v std_term = "'v Standard_Constant allegorical_term"
type_synonym 'v std_sentence = "'v std_term \<times> 'v std_term"
type_synonym ('v,'a) std_graph = "('v Standard_Constant, ('v+'a)) labeled_graph"

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

definition standard :: "('l \<times> 'v) set \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('l, 'v) labeled_graph \<Rightarrow> bool" where
"standard C b t idt G
   \<equiv> G = restrict G
   \<and> vertices G \<noteq> {}
   \<and> ident_rel idt G
   \<and> getRel b G = {}
   \<and> getRel t G = {(x,y). x\<in>vertices G \<and> y\<in>vertices G}
   \<and> (\<forall> (l,v) \<in> C. getRel l G = {(v,v)})"

abbreviation standard' :: "'v set \<Rightarrow> ('v,'a) std_graph \<Rightarrow> bool" where
"standard' C \<equiv> standard ((\<lambda> c. (S_Const c,Inl c)) ` C) S_Bot S_Top S_Idt"

definition model :: "'v set \<Rightarrow> ('v,'a) std_graph \<Rightarrow> ('v std_sentence) set \<Rightarrow> bool" where
"model C G T \<equiv> standard' C G \<and> (\<forall> S \<in> T. G \<Turnstile> S)"

abbreviation consistent :: "'b itself \<Rightarrow> 'v set \<Rightarrow> ('v std_sentence) set \<Rightarrow> bool" where
"consistent _ C T \<equiv> \<exists> (G::('v,'b) std_graph). model C G T"

definition entails :: "'b itself \<Rightarrow> 'v set \<Rightarrow> ('v std_sentence) set \<Rightarrow> 'v std_sentence \<Rightarrow> bool"  where
"entails _ C T S \<equiv> \<forall> (G::('v,'b) std_graph). model C G T \<longrightarrow> G \<Turnstile> S"

lemma standard_top_not_bot[intro]:
"standard' C G \<Longrightarrow> :G:\<lbrakk>\<bottom>\<rbrakk> \<noteq> :G:\<lbrakk>\<top>\<rbrakk>"
  unfolding standard_def by auto

lemma consistent_iff_entails_nonsense: (* Lemma 2 *)
"consistent t C T = (\<not> entails t C T (\<bottom>,\<top>))"
proof
  show "consistent t C T \<Longrightarrow> \<not> entails t C T (\<bottom>, \<top>)"
    using standard_top_not_bot unfolding entails_def model_def
    by fastforce
qed (auto simp:entails_def model_def)

end