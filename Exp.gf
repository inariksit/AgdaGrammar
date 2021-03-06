abstract Exp = {

flags startcat = Decl ;


      -- note, cubical tt doesn't support inductive families, and therefore the datatype (& labels) need to be modified

cat
  Comment ;
  Module  ;
  AIdent ;
  Imp ; --imports, add later
  Decl ; 
  Exp ;
  ExpWhere ;
  Tele ;
  Branch ; 
  PTele ;
  Label ;
  [AIdent]{0} ;
  [Decl]{1} ; 
  [Tele]{0} ;
  [Branch]{1} ; 
  -- [Branch]{0} ; 
  [Label]{1} ;
  [PTele]{1} ; 
  -- [Exp]{1};

  -- I still dont see why [exp] is needed
  -- also, cant use this list notation for bnfc unless I
  -- add a second category

  --cat [C] {n}
  -- =
  --cat ListC ;
  --fun BaseC : C -> ...-> C -> ListC ; -- n C ’s
  --fun ConsC : C -> ListC -> ListC

fun

  DeclDef : AIdent -> [Tele] -> Exp -> ExpWhere -> Decl ;
  DeclData : AIdent -> [Tele] -> [Label] -> Decl ; 
  -- data nat : Set where zero | suc ( n : nat )
  DeclSplit : AIdent -> [Tele] -> Exp -> [Branch] -> Decl ;
  DeclUndef : AIdent -> [Tele] -> Exp -> Decl ;

  Where : Exp -> [Decl] -> ExpWhere ;
  NoWhere : Exp -> ExpWhere ;

  Split : Exp -> [Branch] -> Exp ;
  -- ::= "split@" Exp "with" "{" [Branch] "}" ;
  Let : [Decl] -> Exp -> Exp ;
  Lam : [PTele] -> Exp -> Exp ;
  Fun : Exp -> Exp -> Exp ;
  Pi    : [PTele] -> Exp -> Exp ;
  Sigma : [PTele] -> Exp -> Exp ;
  App : Exp -> Exp -> Exp ;
  Id : Exp -> Exp -> Exp -> Exp ;
  IdJ : Exp -> Exp -> Exp -> Exp -> Exp -> Exp ;
  Fst : Exp -> Exp ;
  Snd : Exp -> Exp ;
  -- Pair : Exp -> [Exp] -> Exp ; -- i think this list is only for the cubical part, so we'll try without for now
  Pair : Exp -> Exp -> Exp ;
  Var : AIdent -> Exp ;          
  Univ : Exp ;
  Refl : Exp ;
  --Hole : HoleIdent -> Exp ; -- need to add holes

  OBranch :  AIdent -> [AIdent] -> ExpWhere -> Branch ;

  OLabel : AIdent -> [Tele] -> Label ;

  -- construct telescope
  TeleC : AIdent -> [AIdent] -> Exp -> Tele ;
  PTeleC : Exp -> Exp -> PTele ;

  A , B , C , D , E , F , G , H , I , J , K , L , M , N , O , P , Q , R , S , T , U , V , W , X , Y , Z : AIdent ;
  -- X , Y , Z , B : AIdent ;

  True , False , Bool : AIdent ;

  CaseBool : AIdent ;
  IndBool : AIdent ;

  FunExt : AIdent ;

  Nat : AIdent ;
  Zero : AIdent ;
  Suc : AIdent ;
  EqualNat : AIdent ;


  Unit : AIdent ;
  Top : AIdent ;

  -- how to resolve this amgiuity
  -- GenAIdent : String -> AIdent ;


}
