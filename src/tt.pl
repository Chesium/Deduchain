:- module(tt,[]).

:- use_module('proof.pl').

% 测试
test :-
  Preds = [
    ['square',4],
    ['ang45',3],
    ['ang90',3],
    ['eqlen',4],
    ['parallel',4],
    ['intersection',5],
    ['rotate_from_tri',6]
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
  initFacts(OriFacts,Facts),

  Steps = [
    [0,ang90(a,d,c)],
    [1,eqlen(a,d,d,c)]
  ],

  proof(Preds,Rules,RuleSets,Facts,Ans,Steps),

true.