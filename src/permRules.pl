:- module(permRules,[
  cycPerm/2,
  rcycPerm/2,
  angPerm/2,
  biPairPerm/2,
  triPairMatchPerm/2,
  itscPerm/2
]).

:- encoding(utf8).

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

itscPerm(X,L) :-
  append([InterPoint],Ls,L),
  biPairPerm(Pls,Ls),
  append([InterPoint],Pls,X).