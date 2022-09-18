theory BoolExp

imports Main

begin

section "Boolean expressions"

datatype boolexp =
  BTrue | 
  BFalse | 
  BIf boolexp boolexp boolexp

definition is_value_bd :: "boolexp \<Rightarrow> bool" where
"is_value_bd t = (case t of BTrue \<Rightarrow> True | BFalse \<Rightarrow> True | _ \<Rightarrow> False)"

inductive beval1 :: "boolexp \<Rightarrow> boolexp \<Rightarrow> bool" where
beval1_if_true: "beval1 (BIf BTrue t2 t3) t2" |
beval1_if_false: "beval1 (BIf BFalse t2 t3) t3" |
beval1_if: "beval1 t1 t1' \<Longrightarrow> beval1 (BIf t1 t2 t3) (BIf t1' t2 t3)"

fun beval1f :: "boolexp \<Rightarrow> boolexp" where
"beval1f (BIf BTrue t2 t3) = t2" |
"beval1f (BIf BFalse t2 t3) = t3" |
"beval1f (BIf t1 t2 t3) = (BIf (beval1f t1) t2 t3)" |
"beval1f t = t"

fun bevalf :: "nat \<Rightarrow> boolexp \<Rightarrow> boolexp" where
"bevalf 0 t = t" | 
"bevalf _ BTrue = BTrue" |
"bevalf _ BFalse = BFalse" |
"bevalf (Suc fuel) t = bevalf fuel (beval1f t)"

theorem beval1f_determinacy: "\<lbrakk>beval1f t = t'; beval1f t = t''\<rbrakk> \<Longrightarrow> t' = t''"
proof(induction t)
  case BTrue
  then show ?case by simp
next
  case BFalse
  then show ?case by simp
next
  case (BIf t1 t2 t3)
  then show ?case by simp
qed

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

theorem "is_value_bd t \<Longrightarrow> is_normal t"
  by (auto simp: is_normal_def is_value_bd_def elim: beval1.cases)

(* BIf case Found with sledgehammer *)
theorem "is_normal t \<Longrightarrow> is_value_bd t"
  unfolding is_normal_def
  unfolding is_value_bd_def
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

export_code beval_ex BTrue in OCaml

end