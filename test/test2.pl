% :- working_directory(_, '../code').
% :-[main].

axiom([+specialNumber(4)]).
axiom([+specialNumber(5)]).
axiom([-specialNumber([func,mySqrt,\x]), +superSpecialNumber(\x)]).
% 16 and 25 are super special numbers

mySqrt(X,Y) :- %Y is output
    Y is integer(sqrt(X)).

%Success: 
    % axiom(X), 
    % length(X,Y), 
    % Y is 2, 
    % !,
    % Z = -P,  
    % nth1(1,X,Z), 
    % P =..L, 
    % L2 = [func, FuncName,_], 
    % nth1(2,L,L2), 
    % call(FuncName,16,Ans). 

%Problem: 
    % 1. how to call this "function" and get the output? (DO I need to?)
    % 2. how to do type conversion e.g. from int to float?
    % 3. how to guarantee the name is not another reserved in our prolog program? (can hard code, deal later)
