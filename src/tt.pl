:- module(tt,[]).


:- encoding(utf8).
:- debug.

:- use_module('proof.pl').

% 测试
test :-
  Preds = [
    ['square',4,rcycPerm],
    ['ang',4,angPerm],
    ['eqlen',4,biPairPerm],
    ['parallel',4,biPairPerm],
    ['intersection',5,itscPerm],
    ['rotate_from_tri',6,triPairMatchPerm],
    ['sameside',4,sidePerm],
    ['diffside',4,sidePerm]
  ],
  Rules = [
    (
      ang(P1,P2,P3,90) :-
        square(P1,P2,P3,X)
    ),
    (
      eqlen(P1,P2,P2,P3) :-
        square(P1,P2,P3,X)
    ),
    (
      ang(P1,P2,P3,D) :-
        eqlen(P1,P2,P1,P3),
        E is 180-2*D,
        ang(P2,P1,P3,E)
    )
  ],
  RuleSets = [
    [0],
    [1],
    [2]
  ],
  OriFacts = [
    square(a,b,c,d),
    eqlen(a,e,a,c),
    parallel(d,e,a,c),
    intersection(f,a,e,c,d),
    rotate_from_tri(a,b,g,a,d,e)
  ],

  Steps = [
    [0,ang(a,d,c,90)],
    [1,eqlen(a,d,d,c)],
    [2,ang(a,c,d,45)]
  ],

  proof:proof(Preds,Rules,RuleSets,OriFacts,Ans,Steps),

true.