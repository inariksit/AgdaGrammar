abstract Exp = {

flags startcat = Decl ;

--what about layout
--cat [C] {n}
-- = 
--cat ListC ;
--fun BaseC : C -> ...-> C -> ListC ; -- n C ’s
--fun ConsC : C -> ListC -> ListC

-- note, cubical tt doesn't support inductive families, and therefore the datatype (& labels) need to be modified

cat
  Comment ;
  Module  ;
  AIdent ;
  Imp ;
  Decl ; 
  Exp ;
  ExpWhere ;
  Tele ;
  Branch ; 
  PTele ;
  Label ;
  [AIdent]{0} ;
  [Decl]{1} ; 
  -- [Tele]{1} ;
  [Tele]{0} ;
  [Branch]{1} ; 
  [PTele]{1} ; 
  [Label]{1} ;


--want telescopes to be arbitrary length
--[Tele] {n} 

fun

  DeclDef : AIdent -> [Tele] -> Exp -> ExpWhere -> Decl ;
  DeclData : AIdent -> [Tele] -> [Label] -> Decl ; 
  DeclSplit : AIdent -> [Tele] -> Exp -> [Branch] -> Decl ;
  DeclUndef : AIdent -> [Tele] -> Exp -> Decl ;

  Where : Exp -> [Decl] -> ExpWhere ;
  NoWhere : Exp -> ExpWhere ;

  Let : [Decl] -> Exp -> Exp ;
  Lam : [PTele] -> Exp -> Exp ;

  -- Split : Exp -> [Branch] -> Exp ;
  Fun : Exp -> Exp -> Exp ;
  Pi    : [PTele] -> Exp -> Exp ;
  Sigma : [PTele] -> Exp -> Exp ;
  App : Exp -> Exp -> Exp ;
  Id : Exp -> Exp -> Exp ;
  IdJ : Exp -> Exp -> Exp -> Exp -> Exp -> Exp ;
  Fst : Exp -> Exp ;
  Snd : Exp -> Exp ;
  -- Pair : Exp -> [Exp] -> Exp ; -- i think this list is only for the cubical part, so we'll try without for now
  Pair : Exp -> Exp -> Exp ;
  Var : AIdent -> Exp ;          
  U : Exp ;
  --Hole : HoleIdent -> Exp ; -- need to add holes

  OBranch :  AIdent -> [AIdent] -> ExpWhere -> Branch ;

  OLabel : AIdent -> [Tele] -> Label ;

  -- construct telescope
  TeleC : AIdent -> [AIdent] -> Exp -> Tele ;
  PTeleC : Exp -> Exp -> PTele ;


  X , Y , Z : AIdent ;

  -- how to resolve this amgiuity
  -- GenAIdent : String -> AIdent ;


}
