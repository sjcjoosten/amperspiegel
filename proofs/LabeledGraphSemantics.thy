theory LabeledGraphSemantics
imports RulesAndChains
begin
(* gets the top relation-label as argument *)
definition top_rule :: "'l \<Rightarrow> ('l,'v::{one,zero,numeral}) Graph_PreRule" where
"top_rule t = (LG {} {0,1},LG {(t,0,1)} {0,1})"

definition nonempty_rule :: "('l,'v::{one,zero,numeral}) Graph_PreRule" where
"nonempty_rule = (LG {} {},LG {} {0})"

(* gets a reflexive relation-label as argument *)
definition reflexivity_rule :: "'l \<Rightarrow> ('l,'v::{one,zero,numeral}) Graph_PreRule" where
"reflexivity_rule t = (LG {} {0},LG {(t,0,0)} {0})"

(* TODO: Show they're all rules *)


definition getRel where
"getRel l G = {(x,y). (l,x,y) \<in> edges G}"

definition standard :: "'l set \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> ('l, 'l) labeled_graph \<Rightarrow> bool" where
"standard C b t idt G
   \<equiv> G = restrict G
   \<and> vertices G \<noteq> {}
   \<and> getRel idt G = {(x,x). x\<in>vertices G}
   \<and> getRel b G = {}
   \<and> getRel t G = {(x,y). x\<in>vertices G \<and> y\<in>vertices G}
   \<and> (\<forall> c \<in> C. getRel c G = {(c,c)})"

(* Work towards Lemma 2, 6 and 7 *)

end