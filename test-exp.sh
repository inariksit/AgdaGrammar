#/usr/bin/bash

natBool='(Fun (Var Nat) (Var Bool))'
natNatBool='(Fun (Var Nat) (Fun (Var Nat) (Var Bool)))'
zero_True='(OBranch Zero BaseAIdent (NoWhere (Var True)))'
zero_False='(OBranch Zero BaseAIdent (NoWhere (Var False)))'
sucN_False='(OBranch Suc (ConsAIdent N BaseAIdent) (NoWhere (Var False)))'
sucN_recurse='(OBranch Suc (ConsAIdent N BaseAIdent) (NoWhere (App (App (Var EqualNat) (Var M)) (Var N))))'


zeroBranch="OBranch
             Zero
             BaseAIdent
             (NoWhere
                (Split $natBool
                       (ConsBranch $zero_True
                                   (BaseBranch $sucN_False))))"
succBranch="OBranch
             Suc
             (ConsAIdent M BaseAIdent)
             (NoWhere
                (Split $natBool
                       (ConsBranch $zero_False
                                   (BaseBranch $sucN_recurse))))"
gflin() {
 gf --run ExpAgda.gf ExpCubicalTT.gf | sed 's/\\/\n/g ; s/ExpAgda: /ExpAgda:\n /g'
}

echo "The two branches"
echo "----------------\n"
echo l -treebank $zeroBranch | gflin
echo l -treebank $succBranch | gflin

fullExp="DeclSplit
           EqualNat
           BaseTele
           $natNatBool
           (ConsBranch ($zeroBranch)
                       (BaseBranch ($succBranch)))"

echo "\nThe full expression"
echo "-------------------\n"
echo l -treebank $fullExp | gflin

#################
# Minimal example

minEx="DeclSplit
           X
           BaseTele
           (Fun (Var Bool) (Var Nat))
           (ConsBranch
                 (OBranch True BaseAIdent (NoWhere (Var Zero)))
              (BaseBranch
                 (OBranch False BaseAIdent (NoWhere (App (Var Suc) (Var Zero))))))"


echo "\nSmall example"
echo "-------------\n"
echo l -treebank $minEx | gflin
