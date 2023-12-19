:- consult('tabox.pl').
/* tabox_auto_referante n'est pas censé fonctionné car autoréférente: */
/* :- consult('tabox_auto_referante.pl').*/

recup_tbox(Ma_tbox) :-
    setof((ConceptNA, Expression), equiv(ConceptNA, Expression), Ma_tbox).
recup_exp_tbox(Concept_non_atomique, Exp) :-
    recup_tbox(Ma_tbox),
    member((Concept_non_atomique, Exp), Ma_tbox), !.

recup_abox(Ma_abox):-
    setof((Instance, Expression), inst(Instance, Expression), Ma_abox).
    
recup_exp_abox(Instance, Exp) :-
    recup_abox(Ma_abox),
    member((Instance, Exp), Ma_abox), !.

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
non_autoref(Concept_non_atomique) :- cnamena(Concept_non_atomique), recup_exp_tbox(Concept_non_atomique, Son_exp) , non_autoref(Concept_tbox, Son_exp).


aucun_autoref([]).
aucun_autoref([H|T]) :- non_autoref(H), aucun_autoref(T).
/* test : non_autoref(sculpteur) */

/* concept, faudrait que je le teste */
/* on fait aussi une vérification de l'expression ? pour cnamena */

concept(Atomique):- cnamea(Atomique). % contient aussi anything et nothing
concept(Non_atomique):- cnamena(Non_atomique).
concept(and(Exp1, Exp2)) :- concept(Exp1), concept(Exp2).
concept(or(Exp1, Exp2)) :- concept(Exp1), concept(Exp1).
concept(not(Exp)) :- concept(Exp).
concept(some(R, C)) :- rname(R) , concept(C).
concept(all(R, C)) :- rname(R) , concept(C).




% supression concept non atom
suppr_concept_nat(Atomique, Atomique):- cnamea(Atomique). % contient aussi anything et nothing
suppr_concept_nat(Non_atomique, Son_exp_sans_nat):- recup_exp_tbox(Non_atomique, Son_exp), suppr_concept_nat(Son_exp, Son_exp_sans_nat).
suppr_concept_nat(and(Exp1, Exp2), and(Exp3, Exp4)) :- suppr_concept_nat(Exp1, Exp3), suppr_concept_nat(Exp2, Exp4).
suppr_concept_nat(or(Exp1, Exp2), or(Exp3, Exp4)) :- suppr_concept_nat(Exp1, Exp3), suppr_concept_nat(Exp2, Exp4).
suppr_concept_nat(not(Exp), not(Exp2)) :- suppr_concept_nat(Exp, Exp2).
suppr_concept_nat(some(R, C), some(R, C2)) :- suppr_concept_nat(C, C2).
suppr_concept_nat(all(R, C), all(R, C2)) :- suppr_concept_nat(C, C2).


%analyse_semantique à tester, je l'ai différencier de concept, c'est pas très clair dans l'exercice
% il faut lui mettre la tbox en paramètre, avec setof, pour analyser la tbox
traitement_Tbox([], []).

traitement_Tbox([(Concept_non_atomique, Exp)|T], [(Concept_non_atomique, NewExpNNF)|NewT]):-
    cnamena(Concept_non_atomique),
    non_autoref(Concept_non_atomique),
    concept(Exp),
    suppr_concept_nat(Exp, NewExp),
    nnf(NewExp, NewExpNNF),
    traitement_Tbox(T, NewT), !.
    
recup_tbox_simplifie(TboxSimplifie) :- 
    recup_tbox(AncienneTbox),
    traitement_Tbox(AncienneTbox, TboxSimplifie).

recup_exp_tbox_simplifie(Concept, SonExp) :-
    recup_tbox_simplifie(TboxSimplifie),
    member((Concept, SonExp), TboxSimplifie), !. % ! pas nécessaire je crois
    
    
traitement_Abox([], []).
traitement_Abox([(Instance, ConceptNonAtomique)|T], [(Instance, SonExpSimplifie)|NouveauT]) :-
    iname(Instance), cnamena(ConceptNonAtomique),
    recup_exp_tbox_simplifie(ConceptNonAtomique, SonExpSimplifie), 
    traitement_Abox(T, NouveauT).
traitement_Abox([(Instance, ConceptAtomique)|T], [(Instance, ConceptAtomique)|NouveauT]) :-
    iname(Instance), cnamea(ConceptAtomique),
    traitement_Abox(T, NouveauT).


recup_abox_simplifie(AboxSimplifie):-
    recup_abox(AncienneAbox),
    traitement_Abox(AncienneAbox, AboxSimplifie), !.
