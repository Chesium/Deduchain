:- module(proof,[
  proof/6,
  initFacts/2
]).

:- encoding(utf8).
:- debug.

:- use_module('permRules.pl').

% 实现 switch 控制语句：若 X==Val 则将 V 存至 X
switch(X,[Val:V|Cases],Dist) :-
  (X == Val ->
    Dist = V
  ;
    switch(X, Cases, Dist)
  ).

% 获取 Fact 的谓词名称，保存至 X
functorName(Fact,X) :-
  Fact =.. L,
  nth0(0,L,X).

% 获取 Fact 的参数列表，保存至 X
functorArgs(Fact,X) :-
  Fact =.. L,
  nth0(0,L,N),
  append([N],X,L).

% 添加一条表示 [名称,元数] 对应谓词永非的规则至 prolog 数据库
assertNeg(Predtuple) :-
  nth0(0,Predtuple,PredName),
  nth0(1,Predtuple,PredArity),
  functor(T,PredName,PredArity),
  term_string(T,Tstr),
  string_concat(Tstr, ' :- fail', Negstr),
  term_string(Neg,Negstr),
  assertz(Neg).

% 检查假设 Hyp 是否存在于包含谓词集 P 的事实库 F 中
alreadyExist(P,F,Hyp) :-
  clearAll(P),
  maplist(assertz,F),
  maplist(assertNeg,P),
  Hyp.

% 在 Lib 规则列表中选取索引为 I 的规则添加至 prolog 数据库中
enableTheory(Lib,I) :-
  nth0(I,Lib,X),
  assertz(X).

% 在包含谓词集 P 的事实库 F 中启用规则库 T 中索引存在于 Is 的所有规则
setTheory(P,F,T,Is) :-
  clearAll(P),
  maplist(assertz,F),
  maplist(enableTheory(T),Is).

% 清除 [名称,元数] 对应谓词的所有子句
clearIndv(Predtuple) :-
  nth0(0,Predtuple,PredName),
  nth0(1,Predtuple,PredArity),
  number_string(PredArity,PredArityStr),
  string_concat(PredName,'/',X),
  string_concat(X,PredArityStr,PredStr),
  term_string(Pred,PredStr),
  abolish(Pred).

% 清除 [名称,元数] 列表中所有谓词的所有子句
clearAll(Preds) :- 
  maplist(clearIndv,Preds).

% 已每行一个事实的形式打印事实库 Facts 中的所有事实
printFact(Facts) :-
  (Facts = [] ->
  (true);
      nth0(0,Facts,First,Rest),
      writeln(First),
      printFact(Rest) % 递归
  ).

% 将事实 Fact 添加至 FactLib 中，一并添加其谓词规定的等价排列形式，结果存至 To
appendFact(FactLib,To,Fact) :- 
  functorName(Fact,Name),
  functorArgs(Fact,Arg),
  switch(Name,[
    'square' : rcycPerm(PArg,Arg),
    'ang45' : angPerm(PArg,Arg),
    'ang90' : angPerm(PArg,Arg),
    'eqlen' : biPairPerm(PArg,Arg),
    'parallel' : biPairPerm(PArg,Arg),
    'intersection' : (
      append([InterPoint],Ls,Arg),
      biPairPerm(Pls,Ls),
      append([InterPoint],Pls,PArg)
    ),
    'rotate_from_tri' : triPairMatchPerm(PArg,Arg)
  ],PermRule),
  (var(PermRule) ->
      PermRule = (PArg = Arg)
  ;true),
  findall(Nfact,(PermRule,append([Name],PArg,NfactL),Nfact =.. NfactL),PL),
  append(FactLib,PL,To).

% 初始化事实库，求出 Facts 中所有事实的所有排列形式，存于 Lib
initFacts(Facts,Lib) :-
  (
    Facts = [] ->
      Lib = []
    ;
      nth0(0,Facts,First,Rest),
      initFacts(Rest,Part), % 递归
      appendFact(Part,Lib,First)
  ).

pFact :- fail.
% 应用规则库 T 中索引存在于 I 中的所有规则，在包含谓词集 P 的事实库 F 中尝试推导 H
% 若成功，则将 H 及其所有排列形式添加至事实库 F 中，结果存于 A
checkddc(P,R,I,F,A,H) :-
  (alreadyExist(P,F,H) ->
    % H 已存在于事实库 F 中，无需进一步推导
    writeln('==Exist==')
  ;
    setTheory(P,F,R,I),
    (H ->
      % 推导成功
      writeln('==OK=='),
      clearAll(P),
      appendFact(F,A,H),
      (pFact->
        writeln('==NOW Facts=='),
        printFact(A)
      ;true)
    ;
      % 推导失败
      writeln('==Wrong=='),
      clearAll(P)
    )
  ).

proof(P,R,RS,F,A,S) :-
  (S = [] ->
    A = F
  ;
    nth0(0,S,N,Rest),
    nth0(0,N,I),
    nth0(1,N,H),
    nth0(I,RS,Is),
    checkddc(P,R,Is,F,X,H),
    proof(P,R,RS,X,A,Rest)
  ).