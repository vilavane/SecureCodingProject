theory IntervalLists
  imports Main

begin
datatype intvl = Bd nat nat | Ub nat


fun inv' :: "nat \<Rightarrow> intvl list \<Rightarrow> bool" where
"inv' n [] = False"
|"inv' n [Bd x y] = (if n<x then True else False)"
|"inv' n [Ub x] = (if n<x then True else False)"
| " inv' a (Ub vb # v # vc) = (if a<vb then inv' vb (v#vc) else False)"
|"inv' a (Bd va vd # vb # vc) = (if a<va then inv' vd (vb#vc) else False)"

definition inv where "inv\<equiv>inv' 0"

fun set_of :: "intvl list \<Rightarrow> nat set" where 
"set_of [] = {}"
|"set_of [Bd x y] = {x..y}"
|"set_of [Ub x] = {x..}"
|"set_of (Ub vb # v # vc) = {vb..} \<union> set_of (v#vc)"
|"set_of (Bd va vd # vb # vc) = {va..vd} \<union> set_of (vb#vc)"

fun add :: "nat \<Rightarrow> intvl list \<Rightarrow> intvl list" where
"add n [] = [Bd n n]"
|"add n [Bd x y] = (if n=x-1 then [Bd n y] else (if n<x-1 then (Bd n n)#[Bd x y] else (if n=y+1 then [Bd x n] else (if n>y+1 then [Bd x y]@[Bd n n] else [Bd x y]))))"
|"add a (Ub vb # va) = (if a=vb-1 then Ub a"

end