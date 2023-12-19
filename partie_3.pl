:- consult('tabox.pl').
:- consult('partie_1.pl').
:-  consult('partie_2.pl').

compteur(1).

troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
resolution(Lie,Lpt,Li,Lu,Ls,Abr),
nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').

tri_Abox([],[],[],[],[],[]).

