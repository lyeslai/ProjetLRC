:- consult('tabox.pl').
% tabox_auto_referante n'est pas censé fonctionné car autoréférente:
% :- consult('tabox_auto_referante.pl').

% Comme dit dans le fichier tabox.pl, ce n'est pas la bonne méthode pour récupérer la tbox
recup_exp_tbox(Concept_non_atomique, Exp) :- tbox(Ma_tbox), member((Concept_non_atomique, Exp), Ma_tbox), !.

% autoref, ne pas oublié le ! 

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

% test : non_autoref(sculpteur)

% concept, faudrait que je le teste

concept(Atomique):- cnamea(Atomique). % contient aussi anything et nothing
concept(Non_atomique):- cnamena(Non_atomique). % on fait aussi une vérification de l'expression ? 
concept(and(Exp1, Exp2)) :- concept(Exp1), concept(Exp2).
concept(or(Exp1, Exp2)) :- concept(Exp1), concept(Exp1).
concept(not(Exp)) :- concept(Exp).
concept(some(R, C)) :- rname(R) , concept(C).
concept(all(R, C)) :- rname(R) , concept(C).

% analyse_semantique à tester, je l'ai différencier de concept, c'est pas très clair dans l'exercice
% il faut lui mettre la tbox en paramètre, avec setof, pour analyser la tbox
analyse_semantique_tbox([]).

analyse_semantique_tbox([(Concept_non_atomique, Exp)|T]):- cnamena(Concept_non_atomique), concept(Exp), analyse_semantique_tbox(T).

% même chose pour la abox, mais avec des setof différent
analyse_semantique_abox_concept([]).
analyse_semantique_abox_concept([(Instance, Concept)|T]):- iname(Instance), cnamea(Concept), analyse_semantique_abox_concept(T).

analyse_semantique_abox_relation([]).
analyse_semantique_abox_relation([(Instance1, Instance2, Relation)|T]):- iname(Instance), iname(Concept), rname(Relation), analyse_semantique_abox_concept(T).

% analyse_semantique_tbox(L):- tbox(L).


% traitement_Tbox, je crois que l'analyse_semantique_tbox fait également automatiquement l'analyse syntaxique, vu qu'il appelle concept.
% ça me parait un peu flou de comment faire pour transformer la tbox, en nouvelle tbox
% Je veux dire, ok, je peux faire en sorte d'avoir une liste tbox, mais même si j'ai une liste, comment l'a transformer en prédicat ?
traitement_Tbox(Liste_Tbox) :- analyse_semantique_tbox(Liste_Tbox). 
