:- consult('tabox.pl').
% n'est pas censé fonctionné :
% :- consult('tabox_auto_referante.pl').
recup_exp_tbox(Concept_non_atomique, Exp) :- tbox(Ma_tbox), member((Concept_non_atomique, Exp), Ma_tbox), !.

% autoref, ne pas oublié le ! 
/* j'ai un petit doute, faut-il regarder dans Liste_dejas_vus ou non ? je pense que non, car ils ont pas de définition */

non_autoref(_, Concept_atomique, _) :- cnamea(Concept_atomique), write(Concept_atomique),  write(', concept atomique\n').
non_autoref(_, Concept_non_atomique , Liste_dejas_vus) :-  cnamena(Concept_non_atomique),
    member(Concept_non_atomique, Liste_dejas_vus),
    recup_exp_tbox(Concept_non_atomique, Son_exp),
    non_autoref(Concept_non_atomique, Son_exp, [Concept_non_atomique|Liste_dejas_vus]), write(Concept_non_atomique), write(', concept non atomique\n').

non_autoref(Nom_de_concept, and(Exp1, Exp2), Liste_dejas_vus):-  non_autoref(Nom_de_concept, Exp1, Liste_dejas_vus) , non_autoref(Nom_de_concept, Exp2, Liste_dejas_vus), write(and(Exp1, Exp2)), write(', and  \n').

non_autoref(Nom_de_concept, or(Exp1, Exp2), Liste_dejas_vus):- non_autoref(Nom_de_concept, Exp1, Liste_dejas_vus) , non_autoref(Nom_de_concept, Exp2, Liste_dejas_vus), write(or(Exp1, Exp2)), write(', or \n').

non_autoref(Nom_de_concept, not(Exp), Liste_dejas_vus):-   non_autoref(Nom_de_concept, Exp, Liste_dejas_vus), write(non(Exp)), write(', non \n').

non_autoref(Nom_de_concept, some(_, Exp), Liste_dejas_vus):-  non_autoref(Nom_de_concept, Exp, Liste_dejas_vus), write(Exp), write(', some \n').
non_autoref(Nom_de_concept, all(_, Exp), Liste_dejas_vus):-  non_autoref(Nom_de_concept, Exp, Liste_dejas_vus), write(Exp), write(', all \n').


non_autoref(Nom_de_concept, Expr):- non_autoref(Nom_de_concept, Expr, [Nom_de_concept]), !.
non_autoref(Concept_tbox) :- cnamena(Concept_tbox), recup_exp_tbox(Concept_tbox, Son_exp) , non_autoref(Concept_tbox, Son_exp), !.
