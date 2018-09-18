theory RuleSemanticsConnection
imports LabeledGraphSemantics RulesAndChains
begin

(* gets the top relation-label as argument *)
definition top_rule :: "'l \<Rightarrow> ('l,'v::{one,zero,numeral}) Graph_PreRule" where
"top_rule t = (LG {} {0,1},LG {(t,0,1)} {0,1})"

definition nonempty_rule :: "('l,'v::{one,zero,numeral}) Graph_PreRule" where
"nonempty_rule = (LG {} {},LG {} {0})"

(* gets a reflexive relation-label as argument *)
definition reflexivity_rule :: "'l \<Rightarrow> ('l,'v::{one,zero,numeral}) Graph_PreRule" where
"reflexivity_rule t = (LG {} {0},LG {(t,0,0)} {0})"

lemma are_rules[intro]:
"graph_rule nonempty_rule"
"graph_rule (top_rule t)"
"graph_rule (reflexivity_rule i)"
  unfolding reflexivity_rule_def top_rule_def nonempty_rule_def is_graph_homomorphism_def
  by auto


(* Work towards Lemma 5 to 7 *)
end