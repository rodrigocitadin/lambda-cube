inductive Term where
  | Var (name : String)
  | Lam (param : String) (body : Term)
  | App (func : Term) (arg : Term)
deriving Repr

#eval Term.Lam "x" (Term.Var "x") -- λx.x
#eval Term.App (Term.Lam "x" (Term.Var "x")) (Term.Var "y") -- (λx.x) y

def substitute (t : Term) (var : String) (value : Term) : Term :=
  match t with
  | Term.Var x => if x = var then value else t
  | Term.Lam x body => if x = var then t else Term.Lam x (substitute body var value)
  | Term.App func arg => Term.App (substitute func var value) (substitute arg var value)

def betaReduce : Term → Term
  | Term.App (Term.Lam x body) arg => substitute body x arg
  | t => t

#eval betaReduce (Term.App (Term.Lam "x" (Term.Var "x")) (Term.Var "y")) -- ((λx.x) y) → y
