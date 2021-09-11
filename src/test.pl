:- encoding(utf8).

:- debug.

:-dynamic x/1.

a(b).
a(c).

x(A):-a(A).

switch(X,[Val:Goal|Cases]) :-
  (X == Val ->
    call(Goal)
  ;
    switch(X, Cases)
  ).


functorName(Fact,X) :-
  Fact =.. L,
  nth0(0,L,X).

perm(F) :-
  F =.. L,
  functorName(F,N),
  append([N],A,L),
  T = (P = A),
  % T = permutation(P,A),
  forall(T,(
    append([N],P,S),
    X =.. S,
    writeln(X),
    assert(X)
  )).

cycPerm(X,L) :-
  append(A,B,L),
  (B=[]->fail;append(B,A,X)).

rcycPerm(X,L) :-
  cycPerm(X,L);
  (
    reverse(L,R),
    cycPerm(X,R)
  ).

angPerm(X,L) :-
  nth0(0,L,A),
  nth0(1,L,B),
  nth0(2,L,C),
  (
    X = [A,B,C];
    X = [C,B,A]
  ).


biPairPerm(X,L) :-
  append([A,B],[C,D],L),
  permutation(P1,[A,B]),
  permutation(P2,[C,D]),
  permutation(P,[P1,P2]),
  append(P,X).

te(PArg,Arg) :-
      append([Inter],Ls,Arg),
      biPairPerm(Pls,Ls),
      append([Inter],Pls,PArg).


triPairMatchPerm(X,L) :-
  permutation(R,[0,1,2]),
  nth0(0,R,I0),
  nth0(1,R,I1),
  nth0(2,R,I2),
  nth0(I0,L,A),
  nth0(I1,L,B),
  nth0(I2,L,C),
  I3 is I0 + 3,
  I4 is I1 + 3,
  I5 is I2 + 3,
  nth0(I3,L,D),
  nth0(I4,L,E),
  nth0(I5,L,F),
  X = [A,B,C,D,E,F].

main:-
  writeln("=begin="),

  % perm(f(a,b,c)).
  % writeln("=end="),
  % abolish(x/1),
  % assertz((x(a))),
  % assertz((x(A):-fail)),

  X = 'd',
  switch(X, [
    'a' : writeln('case1'),
    'b' : writeln('case2'),
    'c' : writeln('case3')
  ]).

  % L =.. [f,a,b,c],
  % term_string(L,S),
  % writeln(S),
main.