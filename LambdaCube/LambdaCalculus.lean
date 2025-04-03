inductive Term
 | var : String → Term
 | abs : String → Term → Term
 | app : Term → Term → Term

 open Term

 def subst (x : String) (s : Term) : Term → Term
  | var y           => if x = y then s else var y
  | abs y t         => if x = y then abs y t else abs y (subst x s t)
  | app t1 t2       => app (subst x s t1) (subst x s t2)

def beta_reduce : Term → Term
 | app (abs x t) s  => subst x s t
 | app t1 t2        => app (beta_reduce t1) (beta_reduce t2)  
 | abs x t          => abs x (beta_reduce t)
 | var x            => var x

#eval beta_reduce (app (abs "x" (var "x")) (var "y")) -- (λx.x) y → y
