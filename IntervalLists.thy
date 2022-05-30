theory IntervalLists
  imports Main

begin
datatype intvl = Bd nat nat | Ub nat


fun first_term :: "intvl \<Rightarrow> nat" where
"first_term (Bd a b) = a"
|"first_term (Ub a) = a"

fun fusion :: "intvl \<Rightarrow> intvl \<Rightarrow>intvl" where
"fusion (Bd a b) (Bd c d) = (Bd a d)"
|"fusion (Bd a b) (Ub c) = (Ub a)"


fun inv' :: "nat \<Rightarrow> intvl list \<Rightarrow> bool" where
"inv' n [] = True"
| " inv' a (Ub x# v) = ((v=[])\<and>(a\<le>x))"
|"inv' a ((Bd x y)#v) =((x\<le>y)\<and>(a\<le>x)\<and>(inv' (y+2) (v)))"

definition inv where "inv\<equiv>inv' 0"

fun set_of :: "intvl list \<Rightarrow> nat set" where 
"set_of [] = {}"
|"set_of (Ub vb # vc) = {vb..} \<union> set_of (vc)"
|"set_of (Bd va vd # vc) = {va..vd} \<union> set_of (vc)"

fun add :: "nat \<Rightarrow> intvl list \<Rightarrow> intvl list" where
"add n [] = [Bd n n]"
|"add n [Bd x y] = (if n+1=x then [Bd n y] else (if n+1<x then (Bd n n)#[Bd x y] else (if n=y+1 then [Bd x n] else (if n>y+1 then [Bd x y]@[Bd n n] else [Bd x y]))))"
|"add a (Ub vb # va) = (if a+1=vb then (Ub a)#va else (if a\<ge>vb then (Ub vb # va) else (Bd a a)#(Ub vb # va) ))"
|"add a (Bd va vd # vb # vc) = (if a+1<va then (Bd a a)#(Bd va vd # vb # vc) else (if a+1=va then (Bd a vd # vb # vc) else (if a=vd+1 then(if ((first_term vb)=a+1) then (fusion (Bd va vd) vb )#vc else (Bd va a # vb # vc))else (Bd va vd)#(add a (vb # vc)) )))"

value "add (19::nat) [(Bd 0 0),(Bd 5 6),(Bd 8 9),(Bd 11 18),(Ub 20)]"

value "add (0::nat) [Bd 0 0, Bd 1 1]"

lemma lemma1:"inv [u]\<Longrightarrow>(first_term u) = y+2 \<Longrightarrow> x\<le>y \<Longrightarrow> set_of ([fusion (Bd x y) u ]) = (set_of [Bd x y]) \<union> {y+1}  \<union>   set_of [u] "
 proof (cases u)
   case (Bd x11 x12)
   assume "inv [u]" and"(first_term u) = y+2"and" x\<le>y"
   with Bd 
 show ?thesis by (auto simp:inv_def)
next
  case (Ub x2)
assume "inv [u]" and"(first_term u) = y+2"and" x\<le>y"
   with Ub
 show ?thesis by (auto simp:inv_def)
qed



theorem "(inv' c  xs) \<Longrightarrow> (a\<ge>c) \<Longrightarrow> set_of (add a xs) = {a} \<union> set_of xs"
proof (induction xs arbitrary: a c rule: add.induct )
  case (1 n)
  then show ?case  by (auto  split :  if_splits)
next
  case (2 n x y)
  then show ?case  by (auto  split :  if_splits simp:inv_def)
next
  case (3 a vb va)
  then show ?case by (auto  split :  if_splits simp:inv_def)
next
  case (4 a va vd vb vc)
  then show ?case apply (auto  split :  if_splits simp:inv_def lemma1)
qed

theorem "(a\<ge>c)\<and> inv' c xs \<Longrightarrow> inv' c (add a xs)"
proof (induction a xs arbitrary: c rule: add.induct )
  case (1 n)
  then show ?case by (auto  split :  if_splits)
next
  case (2 n x y)
  then show ?case by (auto  split :  if_splits)
next
  case (3 a vb va)
  then show ?case by (auto  split :  if_splits)
next
  case (4 a va vd vb vc)
  show ?case
  proof (cases vb)
  case (Bd l r)
  with 4 show ?thesis apply (auto  split : if_splits )
qed


qed



end