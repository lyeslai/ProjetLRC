:- consult('tabox.pl').
:- consult('partie_1.pl').



concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).



enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).


compteur(1).

/*genere(Nom) : génère un nouvel identificateur qui est fourni en sortie dans Nom.*/

genere(Nom) :- compteur(V),nombre(V,L1),
    concat([105,110,115,116],L1,L2),
    V1 is V+1,
    dynamic(compteur/1),
    retract(compteur(V)),
    dynamic(compteur/1),
    assert(compteur(V1)),nl,nl,nl,
    name(Nom,L2).

nombre(0,[]).
nombre(X,L1) :-
    R is (X mod 10),
    Q is ((X-R)//10),
    chiffre_car(R,R1),
    char_code(R1,R2),
    nombre(Q,L),
    concat(L,[R2],L1).
chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').


programe :- premiere_etape(Tbox,Abi,Abr),
            deuxieme_etape(Abi,Abi1,Tbox),
            troisieme_etape(Abi1,Abr).
     


premiere_etape(Tbox, Abi, Abr) :-    
    setof((X,Y),equiv(X,Y),Tbox),
    setof((X,Y),inst(X,Y),Abi),
    setof((X,Y,Z),instR(X,Y,Z),Abr).
                                                         
 
deuxieme_etape(Abi,Abi1,Tbox) :- saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
nl,write('Entrez le numero du type de proposition que vous voulez demontrer :'),
nl,write("1 : Une instance donnee appartient a un concept donne."),
nl,write("2 : Deux concepts nont pas delements en commun(ils ont une intersection vide)."),
nl,read(R),
suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(_,Abi,Abi1,Tbox) :- nl,write('Cette reponse est incorrecte.'),    
                        nl, saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).


acquisition_prop_type1(Abi,Abi1,Tbox):- nl,write("Entrez linstance I : "),
                                    nl,read(I),
                                    nl,write("Entrez le concept C : "),
                                    nl,read(C),
                                    /*Il faut check si c'est un concept et une instanciation*/
                                    /* si c'est pas atomique on doit replacer par la version atomique */
                                    iname(I),
                                    concept(C),
                                    suppr_concept_nat(C,Cnew), 
                                    nnf((not(Cnew)),Result),
                                    Abi1 = [(I,Result) | Abi1].

acquisition_prop_type2(Abi,[(inst,Result)|Abi],_) :- recup_abox(Abi),
                                       nl,write("Entrez le concept C1 : "),
                                        nl,read(C1),
                                        nl,write("Entrez le concept C2 : "),
                                        nl,read(C2),
                                        /*Il faut check si c'est un concept et une instanciation)*/
                                        /* si c'est pas atomique on doit replacer par la version atomique*/
                                        concept(and(C1,C2)),                                        
                                        suppr_concept_nat(C1,C1new),
                                        suppr_concept_nat(C2,C2new),
                                        nnf(and(C1new, C2new),Result),
                                        genere(inst).
                                        
                                       /* nl,write([(inst,Result)|Abi]). */ 


/* partie 3 */

troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
resolution(Lie,Lpt,Li,Lu,Ls,Abr),
nl,write('Youpiiiiii, on a demontre la proposition initiale !!!'), !.                                        

tri_Abox([],[],[],[],[],[]).
tri_Abox([(I, some(R,C)) | L], [(I, some(R,C)) | Lie], Lpt, Li, Lu, Ls) :- tri_Abox(L, Lie, Lpt, Li, Lu, Ls).
tri_Abox([(I, all(R,C)) | L], Lie, [(I, all(R,C)) | Lpt], Li, Lu, Ls) :- tri_Abox(L, Lie, Lpt, Li, Lu, Ls).
tri_Abox([(I, and(C1,C2)) | L], Lie, Lpt, [(I, and(C1,C2)) | Li], Lu, Ls) :- tri_Abox(L, Lie, Lpt, Li, Lu, Ls).
tri_Abox([(I, or(C1,C2)) | L], Lie, Lpt, Li, [(I, or(C1,C2)) | Lu], Ls) :- tri_Abox(L, Lie, Lpt, Li, Lu, Ls).
tri_Abox([(I,C)|L], Lie, Lpt, Li, Lu, [(I,C)|Ls]) :- cnamea(C), tri_Abox(L, Lie, Lpt, Li, Lu, Ls).
tri_Abox([(I,not(C))|L], Lie, Lpt, Li, Lu, [(I,not(C))|Ls]) :- cnamea(C), tri_Abox(L, Lie, Lpt, Li, Lu, Ls).                                        


/* test_clash/1 : predicat qui vaut vrai s'il n'y a pas de clash,
et faux s'il y en a un dans la liste passée en argument */
test_clash([]).
test_clash([(I,C)|T]) :- nnf(not(C),Cnnf), not(member((I,Cnnf),T)), test_clash(T).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- test_clash(Ls), write('test 1') ,complete_some(Lie,Lpt,Li,Lu,Ls,Abr), write('fin test 1'),
                                    test_clash(Ls), write('test 2') , transformation_and(Lie,Lpt,Li,Lu,Ls,Abr),
                                    test_clash(Ls), write('test 3') ,deduction_all(Lie,Lpt,Li,Lu,Ls,Abr),
                                    test_clash(Ls), write('test 4') ,transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).
resolution([],[],[],[],Ls,Abr) :- test_clash(Ls).


/*Affichage de Abox de roles*/
affichage_Abr([]).
affichage_Abr([(A , B , R)| T]) :-  write("<"), write(A), write(","), write(B), write("> : "), write(R), nl, affichage_Abr(Reste).

/*Affichage des liste de la Abox de concept */

affichage([]).
affichage([A|T]):- affichage(A),affichage(T).
affichage(C) :- write(C).
affichage((I,C)) :- nl,write(I), write(' : '), affichage(C).
affichage(not(C)) :- write('¬'),affichage(C).
affichage((I,or(C1,C2))) :- nl,write(I),write(' : '), affichage(C1),write(' ⊔ '),affichage(C2).
affichage((I,and(C1,C2))) :- nl,write(I),write(' : '), affichage(C1),write(' ⊓ '),affichage(C2).
affichage(all(R,C)) :- write('∀'),write(R),write('.'),affichage(C).
affichage(some(R,C)) :- write('∃'), write(R), write('.'), affichage(C).





affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1):-
    write('Affichage Evolution Abox : Abox de Base'),
    nl,affichage(Ls),
    affichage(Lie),
    affichage(Lpt),
    affichage(Li),
    affichage(Lu),
    affichage_Abr(Abr),
    nl,write('ABox Apres'),nl,
    affichage(Ls1),
    affichage(Lie1),
    affichage(Lpt1),
    affichage(Li1),
    affichage(Lu1),
    affichage_Abr(Abr1).

/*Ajout d'un nouvelle assertion dans les listes  Lie, Lpt, Li, Lu ou Ls*/
/*Faut il checker si c'est un cocept ou pas genre concept(some(R,c))*/
evolue((I,C),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu,Ls1):- concat([(I,C)],Ls,Ls1).
/*∃ = Lie*/
evolue((I,some(R,C)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt,Li,Lu,Ls) :- concat([(I,some(R,C))],Lie,Lie1).

/*∀ = Lpt*/
evolue((I,all(R,C)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt1,Li,Lu,Ls) :- concat([(I,all(R,C))],Lpt,Lpt1). 

/*⊓ = Li*/
evolue((I,and(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li1,Lu,Ls) :- concat([(I,and(C1,C2))],Li,Li1).

/*⊔ = Lu*/
evolue((I,or(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu1,Ls) :- concat([(I,or(C1,C2))],Lu,Lu1).

/*not = Ls*/
evolue((I,not(C)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu,Ls1) :- concat([(I,not(C))],Ls,Ls1).




/*Prédicat complete_some cherchant une assertion de concept de la forme (I,some(R,C)) dans Lie*/
complete_some([],_,_,_,_,_).
complete_some([(I,some(R,C))|Lie],Lpt,Li,Lu,Ls,Abr) :- genere(B), /*On génère une instance B*/
                                                    concat([(I,B,R)], Abr, NewAbr), /*ajour de I, B ,R dans Abr*/
													evolue((B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1), /*ajout l'assertion de concept*/
	 											    affiche_evolution_Abox(Ls, [(I,some(R,C))|Lie], Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, [(A,B,R)|Abr]),
												    !,resolution(Lie1, Lpt1, Li1, Lu1, Ls1, NewAbr). /*ajout l'assertion de rôle*/

/*Prédicat transformation_and cherchant une assertion de concept de la forme (I,and(C1,C2)) dans Li*/
transformation_and(_,_,[],_,_,_).
transformation_and(Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls,Abr) :- evolue((I,C1),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
    													   evolue((I,C2),Lie1,Lpt1,Li1,Lu1,Ls1,Lie2,Lpt2,Li2,Lu2,Ls2),
														   nl, affiche_evolution_Abox(Ls, Lie, Lpt, [(I,and(C1,C2))|Li], Lu, Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
														   !,resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr). /*On ajoute à Ls les deux assertions et l'on résoud*/    
                                                              


transformation_or(_,_,_,[],_,_).
transformation_or(Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls,Abr) :-
    % on assert le fait que I est une instance de C1 (première branche)
    evolue((I,C1),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
    nl,
    write('Union\n Première branche : \n'),
    affiche_evolution_Abox(Ls, Lie, Lpt, [(I,or(C1,C2))|Li], Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),!,
    write('\n affichage terminé : \n'),

    % on essaye de résoudre la première branche
    %% write('\n erreur 1 \n'),
    resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr),
    % on assert le fait que I est une instance de C2 (deuxième branche)
    evolue((I,C2),Lie,Lpt,Li,Lu,Ls,Lie2,Lpt2,Li2,Lu2,Ls2),
    write('\n Deuxième branche : \n'),
    affiche_evolution_Abox(Ls, Lie, Lpt, [(I,or(C1,C2))|Li], Lu, Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr), 
    % on essaye de résoudre la deuxième branche
    resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr), !.

liste_instance_relie(_, _, [], []).

liste_instance_relie(Instance1, Relation, [(Instance1, Instance2, Relation)|Abr], [Instance2|Reste_instance_relie] ) :- liste_instance_relie(Instance1, Relation, Abr, Reste_instance_relie).
liste_instance_relie(Instance1, Relation, [(Instance1, _, Mauvaise_relation)|Abr], Liste_instance_relie) :- liste_instance_relie(Instance1, Relation, Abr, Liste_instance_relie).


% ajout d'une liste d'assertion à la abox qui contient les assertions 
ajout_liste_instance_a_abi([], _, Lie,Lpt,Li,Lu,Ls, Lie,Lpt,Li,Lu,Ls).

ajout_liste_instance_a_abi([Instance|Reste_Liste_Instance], Concept, Lie,Lpt,Li,Lu,Ls, Lie_final,Lpt_final,Li_final,Lu_final,Ls_final) :- 
    evolue((Instance, Concept), Lie,Lpt,Li,Lu,Ls, Lie1,Lpt1,Li1,Lu1,Ls1),
    ajout_liste_instance_a_abi(Reste_Liste_Instance, Concept, Lie1,Lpt1,Li1,Lu1,Ls1,  Lie_final,Lpt_final,Li_final,Lu_final,Ls_final).


deduction_all(_,[],_,_,_,_).
deduction_all(Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls,Abr) :-
    % on récupère la liste des instances relié à I
    liste_instance_relie(I, R, Abr, Liste_instance_relie),
    write("Liste relié : \n"),
    write(Liste_instance_relie),
    nl,
    % on assert le fait que ces instance sont des instances de C
    ajout_liste_instance_a_abi(Liste_instance_relie, C, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    % on affiche la liste
    affiche_evolution_Abox(Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls,Abr, Lie1, Lpt1, Li1, Lu1, Ls1, Abr), ! ,
    % on passe à la suite de l'arbre
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr), !.
