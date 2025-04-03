inductive Term
  | var : String → Term
  | abs : String → Term → Term
  | app : Term → Term → Term

open Term

def subst (x : String) (s : Term) : Term → Term
  | var y => if x = y then s else var y
  | abs y t =>
      if x = y then abs y t
      else abs y (subst x s t)
  | app t1 t2 => app (subst x s t1) (subst x s t2)

def beta_step : Term → Option Term
  | app (abs x t) s => some (subst x s t) 
  | app t1 t2 =>
      match beta_step t1 with
      | some t1' => some (app t1' t2)
      | none =>
          match beta_step t2 with
          | some t2' => some (app t1 t2')
          | none => none
  | abs x t =>
      match beta_step t with
      | some t' => some (abs x t')
      | none => none
  | var _ => none

def beta_reduce (t : Term) : Term :=
  match beta_step t with
  | some t' => beta_reduce t'
  | none => t
  decreasing_by
    simp_wf
    sorry

#eval! beta_reduce (app (abs "x" (var "x")) (var "y"))                            -- (λx.x) y → y
#eval! beta_reduce (app (app (abs "x" (abs "y" (var "y"))) (var "x")) (var "z"))  -- (λx.(λy.y) x) z → (λy.y) z → z
