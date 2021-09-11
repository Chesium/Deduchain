:- encoding(utf8).

:- debug.

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

% 在 Lib 规则列表中选取索引为 I 的规则添加至 prolog 数据库中
enableTheory(Lib,I) :-
  nth0(I,Lib,X),
  assertz(X).

% 获取 Fact 的谓词名称，保存至 X
functorName(Fact,X) :-
  Fact =.. L,
  nth0(0,L,X).

% 获取 Fact 的参数列表，保存至 X
functorArgs(Fact,X) :-
  Fact =.. L,
  nth0(0,L,N),
  append([N],X,L).

% 实现 switch 控制语句：若 X==Val 则将 V 存至 X
switch(X,[Val:V|Cases],Dist) :-
  (X == Val ->
    Dist = V
  ;
    switch(X, Cases, Dist)
  ).

% 循环排列：将数列 X 和 L 看作一个数环，若仅使用旋转，X 能与 L 相等，则返回真
cycPerm(X,L) :-
  append(A,B,L),
  (B=[]->fail;append(B,A,X)).

% 扩展循环排列：基本同循环排列，不同的是允许两数列排列方向相反
% 如：[1,2,3,4] 逆序并旋转可得 [2,1,4,3]
rcycPerm(X,L) :-
  cycPerm(X,L);
  (
    reverse(L,R),
    cycPerm(X,R)
  ).

% 角度排列：X 和 L 应为三元组，第一个元素和第三个元素可以互换
angPerm(X,L) :-
  nth0(0,L,A),
  nth0(1,L,B),
  nth0(2,L,C),
  (
    X = [A,B,C];
    X = [C,B,A]
  ).

% 无序双数对排列：X 和 L 应为四元组，前两个元素和后两个元素分别看作一组，两组排列无序，组内排列无序
biPairPerm(X,L) :-
  append([A,B],[C,D],L),
  permutation(P1,[A,B]),
  permutation(P2,[C,D]),
  permutation(P,[P1,P2]),
  append(P,X).

% 顶点对应三角形对排列：X 和 L 应为六元组，前三个元素和后三个元素分别看作一组
% 两组排列无序，组内排列无序，但两组内同索引元素对不变
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

% 在包含谓词集 P 的事实库 F 中启用规则库 T 中索引存在于 Is 的所有规则
setTheory(P,F,T,Is) :-
  clearAll(P),
  maplist(assertz,F),
  maplist(enableTheory(T),Is).

% 应用规则库 T 中索引存在于 TheoryIs 中的所有规则，在包含谓词集 P 的事实库 F 中尝试推导 HypStr
% 若成功，则将 HypStr 及其所有排列形式添加至事实库 F 中，结果存于 Facts
checkddc(P,T,F,TheoryIs,HypStr,Facts) :-
  term_string(Hyp,HypStr),
  (alreadyExist(P,F,Hyp) ->
    % HypStr 已存在于事实库 F 中，无需进一步推导
    writeln('==Exist=='),
  (true);
    setTheory(P,F,T,TheoryIs),
    ((Hyp) ->
      % 推导成功
      writeln('==OK=='),
      clearAll(P),
      appendFact(F,Facts,Hyp),
      writeln('==NOW Facts=='),
      printFact(Facts),
    (true);
      % 推导失败
      writeln('==Wrong=='),
      clearAll(P),
    (true)),
  (true)),
  true.

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

% 已每行一个事实的形式打印事实库 Facts 中的所有事实
printFact(Facts) :-
  (Facts = [] ->
  (true);
      nth0(0,Facts,First,Rest),
      writeln(First),
      printFact(Rest) % 递归
  ).

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
  Theories = [
    (
      ang90(P1,P2,P3) :-
        square(P1,P2,P3,X)
    ),
    (
      eqlen(P1,P2,P2,P3) :-
        square(P1,P2,P3,X)
    )
  ],
  Facts = [
    square(a,b,c,d),
    eqlen(a,e,a,c),
    parallel(d,e,a,c),
    intersection(f,a,e,c,d),
    rotate_from_tri(a,b,g,a,d,e)
  ],
  Iss = [
    [0],
    [1]
  ],
  nth0(0,Iss,Is),
  initFacts(Facts,FF),
  printFact(FF),
  checkddc(Preds,Theories,FF,Is,'ang90(a,d,c)',Ans),
  true.