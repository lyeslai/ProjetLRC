:- consult('tabox.pl').
:- consult('partie_1.pl').


concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).
————————————————————————————————————————
————————————————————————————————————————
/*enleve(X,L1,L2) : supprime X de la liste L1 et renvoie la liste résultante dans L2.*/
————————————————————————————————————————
enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).
————————————————————————————————————————
————————————————————————————————————————
/*genere(Nom) : génère un nouvel identificateur qui est fourni en sortie dans Nom.*/
————————————————————————————————————————
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
chiffre_car(9,’9’).


programe :- premiere_etape(Tbox,Abi,Abr),
            deuxieme_etape(Abi,Abi1,Tbox),
            trosieme_etape(Abi1,Abr).


premiere_etape(Tbox, Abi, Abr) :-    
    setof((X,Y),equiv(X,Y),Tbox),
    setof((X,Y),inst(X,Y),Abi),
    setof((X,Y,Z),instR(X,Y,Z),Abr).
                                                         
 
deuxieme_etape(Abi,Abi1,Tbox) :- saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
nl,write('Entrez le numero du type de proposition que vous voulez demontrer :'),
nl,write("1 : Une instance donnee appartient a un concept donne.")
nl,write("2 : Deux concepts nont pas delements en commun(ils ont une intersection vide).")
nl,read(R),
suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(_,Abi,Abi1,Tbox) :- nl,write('Cette reponse est incorrecte.'),    
                        nl, saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).


acquisition_prop_type1(Abi,Abi1,_):- nl,write("Entrez l'instance I : "),
                                    nl,read(I),
                                    nl,write("Entrez le concept C : "),
                                    nl,read(C),
                                /*Il faut check si c'est un concept et une instanciation)*/
                                /* si c'est pas atomique on doit replacer par la version atomique */
                                    nnf((not(C)),Result),
                                    Abi1 = [(I,Result) | Abi1].

acquisition_prop_type2(Abi,Abi1,Tbox) :- nl,write("Entrez le concept C1 : "),
                                        nl,read(C1),
                                        nl,write("Entrez le concept C2 : "),
                                        nl,read(C2),
                                        /*Il faut check si c'est un concept et une instanciation)*/
                                /* si c'est pas atomique on doit replacer par la version atomique */
                                        nnf(and(C1,C2),Result),
                                        genere(inst),
                                        Abi1=[(I,Result)|Abi1].





/* remplace_cnamena(A,A) :- cnamea(A),!. 
remplace_cnamena(A,X) :- cnamena(A), equiv(A,B), remplace_cnamena(B,X),!.
remplace_cnamena(and(A,B),X) :- remplace_cnamena(A,R1), remplace_cnamena(B,R2), X=and(R1,R2),!.
remplace_cnamena(or(A,B),X) :- remplace_cnamena(A,R1), remplace_cnamena(B,R2), X=or(R1,R2),!.
remplace_cnamena(not(A),X) :- remplace_cnamena(A,R), X=not(R),!.
remplace_cnamena(some(R,C),some(R,R2)) :- rname(R), remplace_cnamena(C,R2), X=some(R,R2),!.
remplace_cnamena(all(R,C),all(R,R2)) :- rname(R), remplace_cnamena(C,R2), X=all(R,R2),!.
*/