concrete ExpAgda of Exp = open Prelude, FormalTwo in {

lincat
  Comment,
  Module ,
  AIdent,
  Imp,
  Decl ,
  ExpWhere,
  Tele,
  PTele,
  Label,
  Branch,
  [Decl] ,
  [Tele],
  [PTele],
  [Label]
    = Str ;
  Exp = TermPrec ;

  -- Inari's changes to lincats
  [Branch] = {s1, s2 : Str} ;
  [AIdent] = IdentList ;

oper
  IdentList : Type = {s : Str ; listSize : ListSize} ;
param
  ListSize = Empty | Nonempty ;
lin

  DeclDef a lt e ew = a ++ lt ++ ":" ++ usePrec 0 e ++ "=" ++ ew ;
  DeclData a t d = "data" ++ a ++ t ++ ": Set where" ++ d ;

  -- Inari's changes, so that it works for only a single split, no recursion
  DeclSplit funName teles type branches =
    funName ++ ":" ++ type.s ++ "\\" ++
    funName ++ branches.s1 ++ "\\" ++
    funName ++ branches.s2 ;

  -- Need to adjust [Branch] accordingly
  BaseBranch x = {s1 = "" ; s2 = x} ;
  ConsBranch x xs = xs ** {s1 = x ++ xs.s1} ; -- not supposed to work for recursive case

  -- Let's also change the syntax for OBranch
  OBranch f xs whereClause = varName f xs ++ "=" ++ whereClause ;

  -- And add parameter to [AIdent] so we know if it's empty
  BaseAIdent = {s = "" ; listSize = Empty} ;
  ConsAIdent x xs = {s = x ++ xs.s ; listSize = Nonempty} ;

  oper
    varName : Str -> IdentList -> Str = \funName,args -> case args.listSize of {
      Nonempty => funName ++ "(" ++ args.s ++ ")" ;
      Empty => funName } ; -- no args

  {- Let's test. Postprocessed \\ into \n.

 l DeclSplit X BaseTele (Fun (Var Bool) (Var Nat)) (ConsBranch (OBranch True BaseAIdent (NoWhere (Var Zero))) (BaseBranch (OBranch False BaseAIdent (NoWhere (App (Var Suc) (Var Zero))))))
ExpAgda: x : ( bool ) -> ( nat )
         x true = zero
         x false = ( suc ) ( zero )
ExpCubicalTT: x : ( bool ) -> ( nat ) = split true -> zero || false -> ( suc ) ( zero )

However, this is not a scalable solution. The small example works only because I have added two fields in the lincat of [Branch]. If the function split in any more than two, we couldn't retain all branches. This is completely garbled:

l DeclSplit EqualNat BaseTele (Fun (Var Nat) (Fun (Var Nat) (Var Bool))) (ConsBranch (OBranch Zero BaseAIdent (NoWhere (Split (Fun (Var Nat) (Var Bool)) (ConsBranch (OBranch Zero BaseAIdent (NoWhere (Var True))) (BaseBranch (OBranch Suc (ConsAIdent N BaseAIdent) (NoWhere (Var False)))))))) (BaseBranch (OBranch Suc (ConsAIdent M BaseAIdent) (NoWhere (Split (Fun (Var Nat) (Var Bool)) (ConsBranch (OBranch Zero BaseAIdent (NoWhere (Var False))) (BaseBranch (OBranch Suc (ConsAIdent N BaseAIdent) (NoWhere (App (App (Var EqualNat) (Var M)) (Var N)))))))))))
ExpAgda:
 equalNat : ( nat ) -> ( ( nat ) -> ( bool ) )
 equalNat zero = zero = true
 suc ( n ) = false
 equalNat suc ( m ) = zero = false
 suc ( n ) = ( ( equalNat ) ( m ) ) ( n )

In the lins, I assumed that all Branches just contain a neat "varName = Value". In reality, that value can actually be another Branch.

So a better solution would be to create a new abstract syntax fun that is better suited to express the Agda syntax for case split. Think like Pred and PredAdv in gf-radio, or Has, HasInside and HasOnTop in my blog post. Same or similar type signature, but different linearisation. (In this case, I think the type signature needs to be different.)



-}

    -- Here we see already that something's going wrong. We would need to keep the two branches separate, because ultimately we want to prefix both with the function name whose branches they are. But we have no access to the function name here (and we can't put a function Str -> Str here.)
lin
  Split exp branches = exp ** {s = branches.s1 ++ "\\" ++ branches.s2} ;


  -- Here end Inari's changes
  ---------------------------

lin
-- Original DeclSplit
--  DeclSplit ai lt e lb = ai ++ lt ++ ":" ++ usePrec 0 e ++ "= split" ++ lb ;
  DeclUndef a lt e = a ++ lt ++ ":" ++ usePrec 0 e ++ "= undefined" ; -- postulate in agda

  Where e ld = usePrec 0 e ++ "where" ++ ld ;
  NoWhere e = usePrec 0 e ;

  Let ld e = mkPrec 0 ("let" ++ ld ++ "in" ++ (usePrec 0 e)) ;
  Lam pt e = mkPrec 0 ("\\" ++ pt ++ "->" ++ usePrec 0 e) ;
  Fun = infixr 1 "->" ; -- A -> Set
  Pi pt e = mkPrec 1 (pt ++ "->" ++ usePrec 1 e) ;
  Sigma pt e = mkPrec 1 (pt ++ "*" ++ usePrec 1 e) ;
  App = infixl 2 "" ;
  Id e1 e2 e3 = mkPrec 3 (usePrec 4 e1 ++ usePrec 4 e2 ++ "==" ++ usePrec 3 e2) ;
  IdJ e1 e2 e3 e4 e5 = mkPrec 3 ("J" ++ usePrec 4 e1 ++ usePrec 4 e2 ++ usePrec 4 e3 ++ usePrec 4 e4 ++ usePrec 4 e5) ;
  Fst e = mkPrec 4 ("proj1" ++ usePrec 4 e) ;
  Snd e = mkPrec 4 ("proj2" ++ usePrec 4 e) ;
  Pair e1 e2 = mkPrec 5 ("(" ++ usePrec 0 e1 ++ "," ++ usePrec 0 e2 ++ ")") ;
  Var a = constant a ;
  Univ = constant "Set" ;
  Refl = constant "refl" ;


  -- [Decl] only used in ExpWhere
  BaseDecl x = x ;
  ConsDecl x xs = x ++ "\n" ++ xs ;

  -- maybe accomodate so split on empty type just gives ()
  -- BaseBranch = "" ;
  -- BaseBranch x = x ;
  -- -- ConsBranch x xs = x ++ "\n" ++ xs ;
  -- ConsBranch x xs = x ++ "||" ++ xs ;

  -- for data constructors
  BaseLabel x = x ;
  ConsLabel x xs = x ++ "|" ++ xs ;

  BasePTele x = x ;
  ConsPTele x xs = x ++ xs ;

  BaseTele = "" ;
  ConsTele x xs = x ++ xs ;

-- Original OBranch
--  OBranch a la ew = a ++ la ++ "->" ++ ew ;
  TeleC a la e = "(" ++ varName a la ++ ":" ++ usePrec 0 e ++ ")" ;
  PTeleC e1 e2 = "(" ++ top e1 ++ ":" ++ top e2 ++ ")" ;

  OLabel a lt = a ++ lt ;

  --object language syntax, all variables for now

  Bool = "bool" ;
  True = "true" ;
  False = "false" ;
  CaseBool = "caseBool" ;
  IndBool = "indBool" ;

  A = "a" ;
  B = "b" ;
  C = "c" ;
  D = "d" ;
  E = "e" ;
  F = "f" ;
  G = "g" ;
  H = "h" ;
  I = "i" ;
  J = "j" ;
  K = "k" ;
  L = "l" ;
  M = "m" ;
  N = "n" ;
  O = "o" ;
  P = "p" ;
  Q = "q" ;
  R = "r" ;
  S = "s" ;
  T = "t" ;
  U = "u" ;
  V = "v" ;
  W = "w" ;
  X = "x" ;
  Y = "y" ;
  Z = "z" ;
  Zero = "zero" ;
  Suc = "suc" ;
  Nat = "nat" ;
  EqualNat = "equalNat" ;

}
