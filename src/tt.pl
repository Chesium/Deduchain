:- module(tt,[]).


:- encoding(utf8).
:- debug.

:- use_module('proof.pl').

% 测试
test :-
  Preds = [
    ['square',4,rcycPerm],
    ['ang45',3,angPerm],
    ['ang90',3,angPerm],
    ['eqlen',4,biPairPerm],
    ['parallel',4,biPairPerm],
    ['intersection',5,itscPerm],
    ['rotate_from_tri',6,triPairMatchPerm]
  ],
  Rules = [
    (
      ang90(P1,P2,P3) :-
        square(P1,P2,P3,X)
    ),
    (
      eqlen(P1,P2,P2,P3) :-
        square(P1,P2,P3,X)
    )
  ],
  RuleSets = [
    [0],
    [1]
  ],
  OriFacts = [
    square(a,b,c,d),
    eqlen(a,e,a,c),
    parallel(d,e,a,c),
    intersection(f,a,e,c,d),
    rotate_from_tri(a,b,g,a,d,e)
  ],

  Steps = [
    [0,ang90(a,d,c)],
    [1,eqlen(a,d,d,c)]
  ],

  proof:proof(Preds,Rules,RuleSets,OriFacts,Ans,Steps),

true.