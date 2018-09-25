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

lemma sentence_iff: (* Lemma 1 *)
  "G \<tturnstile> e\<^sub>1 \<sqsubseteq> e\<^sub>2 = (:G:\<lbrakk>e\<^sub>1\<rbrakk> \<subseteq> :G:\<lbrakk>e\<^sub>2\<rbrakk>)"
  "G \<tturnstile> (e\<^sub>1, e\<^sub>2) = (G \<tturnstile> e\<^sub>1 \<sqsubseteq> e\<^sub>2 \<and> G \<tturnstile> e\<^sub>2 \<sqsubseteq> e\<^sub>1)"
  by auto



end