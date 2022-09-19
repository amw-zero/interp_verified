theory BoolExp

imports Main

begin

section "Boolean expressions"

datatype boolexp =
  BTrue | 
  BFalse | 
  BIf boolexp boolexp boolexp

definition is_value :: "boolexp \<Rightarrow> bool" where
"is_value t = (case t of BTrue \<Rightarrow> True | BFalse \<Rightarrow> True | _ \<Rightarrow> False)"

inductive beval1 :: "boolexp \<Rightarrow> boolexp \<Rightarrow> bool" where
beval1_if_true: "beval1 (BIf BTrue t2 t3) t2" |
beval1_if_false: "beval1 (BIf BFalse t2 t3) t3" |
beval1_if: "beval1 t1 t1' \<Longrightarrow> beval1 (BIf t1 t2 t3) (BIf t1' t2 t3)"

code_pred beval1 .

(*export_code beval1 in OCaml*)

definition "nested_if =
  (BIf (BIf BTrue BFalse BTrue) BTrue BFalse)"

values "{t. beval1 (BIf BFalse BTrue BFalse) t}"

values "{t. beval1 nested_if t}"

values "{t. beval1 BTrue t}"

(* beval1_if case Using Sledgehammer *)
theorem beval1_determinacy:
  "\<lbrakk> beval1 t t'; beval1 t t''\<rbrakk> \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: beval1.induct)
  case (beval1_if_true t2 t3)
  then show ?case by (auto elim: beval1.cases)
next
  case (beval1_if_false t2 t3)
  then show ?case by (auto elim: beval1.cases)
next
  case (beval1_if t1 t1' t2 t3)
  then show ?case
    by (smt (verit, del_insts) beval1.simps boolexp.distinct(4) boolexp.distinct(6) boolexp.inject)
qed

section "Normal form"

definition is_normal :: "boolexp \<Rightarrow> bool" where
"is_normal b \<equiv> \<forall>t. \<not>(beval1 b t)"

theorem "is_value t \<Longrightarrow> is_normal t"
  by (auto simp: is_normal_def is_value_def elim: beval1.cases)

(* BIf case Found with sledgehammer *)
theorem "is_normal t \<Longrightarrow> is_value t"
  unfolding is_normal_def
  unfolding is_value_def
proof (induction t)
  case BTrue
  then show ?case by simp
next
  case BFalse
  then show ?case by simp
next
  case (BIf t1 t2 t3)
  then show ?case
    by (metis beval1_if beval1_if_false beval1_if_true boolexp.exhaust boolexp.simps(10))
qed

inductive beval :: "boolexp \<Rightarrow> boolexp \<Rightarrow> bool" where
once: "beval1 t t' \<Longrightarrow> beval t t'" |
reflexive: "beval t t" |
transitive: "beval t t' \<Longrightarrow> beval t' t'' \<Longrightarrow> beval t t''"

code_pred (modes: i => o => bool as beval') beval . 

definition "beval_ex t = Predicate.the (beval' t)"

(*export_code beval_ex BTrue in OCaml file_prefix "core"*)

(*value "beval_ex (BIf BTrue BTrue BFalse)"*)

values "{ t. beval1 (BIf BTrue BTrue BFalse) t }"

inductive beval_st :: "boolexp \<Rightarrow> boolexp \<Rightarrow> bool" where
b_reflexive: "beval_st t t" |
b_step: "beval1 t t' \<Longrightarrow> beval_st t' t'' \<Longrightarrow> beval_st t t''"

code_pred (modes: i => o => bool as beval_st') beval_st . 

definition "beval_st_ex t = Predicate.the (beval_st' t)"

value "beval_st_ex BTrue"

inductive bigstep :: "boolexp \<Rightarrow> boolexp \<Rightarrow> bool" where
bval: "is_value t \<Longrightarrow> bigstep t t" |
bif_true: "\<lbrakk> bigstep t1 BTrue; bigstep t2 v\<rbrakk> \<Longrightarrow> bigstep (BIf t1 t2 t3) v" |
bif_false: "\<lbrakk> bigstep t1 BFalse; bigstep t3 v\<rbrakk> \<Longrightarrow> bigstep (BIf t1 t2 t3) v"

theorem "\<lbrakk>bigstep t t'; bigstep t t''\<rbrakk> \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: bigstep.induct)
  case (bval t)
  then show ?case
    by (metis bigstep.cases boolexp.simps(10) is_value_def)
next
  case (bif_true t1 t2 v t3)
  then show ?case
    by (smt (verit, best) bigstep.cases boolexp.distinct(1) boolexp.inject boolexp.simps(10) is_value_def)
next
  case (bif_false t1 t3 v t2)
  then show ?case
    by (smt (verit) bigstep.cases boolexp.distinct(1) boolexp.inject boolexp.simps(10) is_value_def)
qed

code_pred (modes: i => o => bool as bigstep') bigstep . 

definition "bigstep_ex t = Predicate.the (bigstep' t)"

value "bigstep_ex (BIf BTrue BTrue BFalse)"

export_code bigstep_ex BTrue in OCaml file_prefix "core"

end