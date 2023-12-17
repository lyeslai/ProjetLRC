cnamena(sculpture).
cnamena(sculpteur).
cnamea(objet).
cnamea(personne).
rname(creerPar).
rname(aCree).
equiv(sculpture,and(objet, all(creePar , sculpture))).
equiv(sculpteur,and(personne,some(aCree,sculpture))).
tbox([(sculpture,and(objet, all(creePar , sculpture))), (sculpteur,and(personne,some(aCree,sculpture)))]).
