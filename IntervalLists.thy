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




end