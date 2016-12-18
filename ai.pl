/*
path (origin, possible paths)
state(x, y, g, h)
visited(source, destination)
explored(x,y,g,h) << Queue
*/

path(-,state(0,0,0,6)).
path(state(0,0,0,6),state(4,0,4,5),state(0,3,3,5)).
path(state(4,0,4,5),state(1,3,7,4),state(4,3,7,4)).
path(state(0,3,3,5),state(4,3,7,4),state(3,0,6,4)).
path(state(1,3,7,4),state(4,3,10,4),state(1,0,10,3)).
path(state(4,3,7,4)).
path(state(3,0,6,4),state(3,3,9,3)).
path(state(1,0,10,3),state(0,1,11,2)).
path(state(3,3,9,3),state(4,2,10,2)).
path(state(4,2,10,2),state(0,2,14,1)).
path(state(0,1,11,2),state(4,1,15,1)).
path(state(4,1,15,1),state(2,3,17,0)).
path(state(0,2,14,1),state(2,0,16,0)).

statecheck(Gr, Hr, CurF)	:-
	ExpF is Gr + Hr,
	CurF =< ExpF.

statecheckr(ExpF, Gr, Hr)	:-
	NxpF is Gr + Hr,
	ExpF =< NxpF.
	
go(T1,T2,T3,T4)	:-
	write('X is : '),
	write(T1),
	write(' Y is : '),
	write(T2),
	write(' G is : '),
	write(T3),
	write(' H is : '),
	write(T4), write('.'), nl.

% Rule With Queue :
	
state(A,B,C,D)	:-
	\+ D =:= 0,
	path(state(A,B,C,D)),
	explored(U,I,O,P),
	ExpF is O + P,
	forall(explored(_,_,Gr,Hr), statecheckr(ExpF, Gr, Hr)),
	retract(explored(U,I,O,P)),
	write('Current node is : ('), write(U), write(','), write(I),write(') '),
	write('with F of '), write(ExpF), write(' as H = '), write(P), write(' and G = ') ,write(O), nl,
	assert(visited(state(A,B,C,D),state(U,I,O,P))),
	state(U,I,O,P).
	
state(A,B,C,D) :-
	\+ D =:= 0,
	path(state(A,B,C,D), state(Z,X,V,N)),
	explored(U,I,O,P),
	CurF is V + N,
	ExpF is O + P,
	%forall(explored(T1,T2,T3,T4), go(T1,T2,T3,T4)),
	forall(explored(_,_,Gr,Hr), statecheck(O,P , CurF)),
	write('Current node is : ('), write(Z), write(','), write(X),write(') '),
	write('with F of '), write(CurF), write(' as H = '), write(N), write(' and G = ') ,write(V), nl,
	assert(visited(state(A,B,C,D),state(Z,X,V,N))),
	state(Z,X,V,N).
	
state(A,B,C,D) :-
	\+ D =:= 0,
	path(state(A,B,C,D), state(Z,X,V,N)),
	explored(U,I,O,P),
	CurF is V + N,
	ExpF is O + P,
	%forall(explored(T1,T2,T3,T4), go(T1,T2,T3,T4)),
	forall(explored(_,_,Gr,Hr), statecheckr(ExpF, Gr, Hr)),
	/*(
			explored(Z,X,_,_)
		->	(
					forall(explored(Z,X,Ga,Ha), statecheck(Ga,Ha , CurF))
				->	assert(explored(Z,X,V,N))
			)
		;	assert(explored(Z,X,V,N))
	),*/
	assert(explored(Z,X,V,N)),
	retract(explored(U,I,O,P)),
	%write('statequeue s1-5'), nl,
	write('Current node is : ('), write(U), write(','), write(I),write(') '),
	write('with F of '), write(ExpF), write(' as H = '), write(P), write(' and G = ') ,write(O), nl,
	assert(visited(state(A,B,C,D),state(U,I,O,P))),
	state(U,I,O,P).
	
state(A,B,C,D) :-
	\+ D =:= 0,
	path(state(A,B,C,D), state(Z,X,V,N), state(S,F,G,H)),
	explored(U,I,O,P),
	CurF is V + N,
	NewF is G + H,
	ExpF is O + P,
	CurF =< NewF,
	%forall(explored(T1,T2,T3,T4), go(T1,T2,T3,T4)),
	forall(explored(_,_,Gr,Hr), statecheck(Gr, Hr, CurF)),
	/*(
			explored(S,F,_,_)
		->	(
					forall(explored(Z,X,Ga,Ha), statecheck(Ga,Ha , CurF))
				->	assert(explored(S,F,G,H))
			)
		;	assert(explored(S,F,G,H))
	),*/
	assert(explored(S,F,G,H)),
	write('Current node is : ('), write(Z), write(','), write(X),write(') '),
	write('with F of '), write(CurF), write(' as H = '), write(N), write(' and G = ') ,write(V), nl,
	assert(visited(state(A,B,C,D),state(Z,X,V,N))),
	state(Z,X,V,N).
	
state(A,B,C,D) :-
	\+ D =:= 0,
	path(state(A,B,C,D), state(Z,X,V,N), state(S,F,G,H)),
	explored(U,I,O,P),
	CurF is V + N,
	NewF is G + H,
	ExpF is O + P,
	CurF >= NewF,
	%forall(explored(T1,T2,T3,T4), go(T1,T2,T3,T4)),
	forall(explored(_,_,Gr,Hr), statecheck(Gr, Hr, NewF)),
	%ExpF >= NewF,
	/*(
			explored(Z,X,_,_)
		->	(
					forall(explored(Z,X,Ga,Ha), statecheck(Ga,Ha , CurF))
				->	assert(explored(Z,X,V,N))
			)
		;	assert(explored(Z,X,V,N))
	),*/
	assert(explored(Z,X,V,N)),
	write('Current node is : ('), write(S), write(','), write(F),write(') '),
	write('with F of '), write(NewF), write(' as H = '), write(H), write(' and G = ') ,write(G), nl,
	assert(visited(state(A,B,C,D),state(S,F,G,H))),
	state(S,F,G,H).
	
state(A,B,C,D) :-
	\+ D =:= 0,
	path(state(A,B,C,D), state(Z,X,V,N), state(S,F,G,H)),
	explored(U,I,O,P),
	CurF is V + N,
	NewF is G + H,
	ExpF is O + P,
	CurF >= ExpF,
	NewF >= ExpF,
	%forall(explored(T1,T2,T3,T4), go(T1,T2,T3,T4)),
	forall(explored(_,_,Gr,Hr), statecheckr(ExpF,Gr,Hr)),
	/*(
			explored(Z,X,_,_)
		->	(		forall(explored(Z,X,Ga,Ha), statecheck(Ga,Ha , CurF))
				->	assert(explored(Z,X,V,N)),
					assert(explored(S,F,G,H))
			)
		;	assert(explored(Z,X,V,N)),
			assert(explored(S,F,G,H))
	),*/
	assert(explored(Z,X,V,N)),
	assert(explored(S,F,G,H)),
	retract(explored(U,I,O,P)),
	write('Current node is : ('), write(U), write(','), write(I),write(') '),
	write('with F of '), write(ExpF), write(' as H = '), write(P), write(' and G = ') ,write(O), nl,
	assert(visited(state(A,B,C,D),state(U,I,O,P))),
	state(U,I,O,P).

% Rule With Empty Queue :

state(A,B,C,D) :-
	\+ D =:= 0,
	path(state(A,B,C,D), state(Z,X,V,N)),
	\+ explored(U,I,O,P),
	RealF is V + N,
	write('Current node is : ('), write(Z), write(','), write(X),write(') '),
	write('with F of '), write(RealF), write(' as H = '), write(N), write(' and G = ') ,write(V), nl,
	assert(visited(state(A,B,C,D),state(Z,X,V,N))),
	state(Z,X,V,N).
	
state(A,B,C,D) :-
	\+ D =:= 0,
	path(state(A,B,C,D), state(Z,X,V,N), state(S,F,G,H)),
	\+ explored(U,I,O,P),
	CurF is V + N,
	NewF is G + H,
	CurF =< NewF,
	assert(explored(S,F,G,H)),
	write('Current node is : ('), write(Z), write(','), write(X),write(') '),
	write('with F of '), write(CurF), write(' as H = '), write(N), write(' and G = ') ,write(V), nl,
	assert(visited(state(A,B,C,D),state(Z,X,V,N))),
	state(Z,X,V,N).
	
state(A,B,C,D) :-
	\+ D =:= 0,
	path(state(A,B,C,D), state(Z,X,V,N), state(S,F,G,H)),
	\+ explored(U,I,O,P),
	CurF is V + N,
	NewF is G + H,
	CurF >= NewF,
	assert(explored(Z,X,V,N)),
	write('Current node is : ('), write(S), write(','), write(F),write(') '),
	write('with F of '), write(NewF), write(' as H = '), write(H), write(' and G = ') ,write(G), nl,
	assert(visited(state(A,B,C,D),state(S,F,G,H))),
	state(S,F,G,H).

state(A,B,C,D)	:-
	D =:= 0,
	F is C + D, nl,
	write('The 4 gallon jug is now : '), write(A), write('.'), nl,
	write('Problem Solved.'), nl, nl,
	end.
	%write('Type \'end.\' to clear data. '), nl.
	
initial :-
	path(-,state(A,B,C,D)),
	F is C + D, nl,
	write('TAI 2151 - Artificial Intelligence Fundamentals'), nl,
	write('This program is written in Prolog by Timothy C. Lam'), nl, nl,
	write('First explorable node is ('), write(A), write(','), write(B), write(') '),
	write('with F of '), write(F), write(' as H = '), write(D), write(' and G = ') ,write(C), nl,
	assert(visited(-,state(0,0,0,6))),
	state(A,B,C,D).
	
end :-
	retractall(visited(_,_)),
	retractall(explored(_,_,_,_)).
	
:- dynamic(explored/4).