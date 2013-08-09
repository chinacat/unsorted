
member(X,[X|_]).
member(X,[_|Y]) :- member(X,Y).

nextto(L, R, Lst) :- iright(L, R, Lst).
nextto(L, R, Lst) :- iright(R, L, Lst).

iright(L, R, [L, R | _]).
iright(L, R, [_ | Rst]) :- iright(L, R, Rst).

zebra(H, W, Z) :-
  H = [[house,norwegian,_,_,_,_],_,[house,_,_,_,milk,_],_,_],
  member([house,englishman,_,_,_,red],H),
  member([house,spaniard,dog,_,_,_],H),
  member([house,_,_,_,coffee,green],H),
  member([house,ukranian,_,_,tea,_],H),

  iright([house,_,_,_,_,ivory],[house,_,_,_,_,green],H),
  member([house,_,snails,winston,_,_],H),
  member([house,_,_,kools,_,yellow],H),
  nextto([house,_,_,chesterfield,_,_],[house,_,fox,_,_,_],H),
  nextto([house,_,_,kools,_,_],[house,_,horse,_,_,_],H),

  member([house,_,_,luckystrike,orange_juice,_],H),
  member([house,japanese,_,parliaments,_,_],H),
  nextto([house,norwegian,_,_,_,_],[house,_,_,_,_,blue],H),
  member([house,W,_,_,water,_],H),
  member([house,Z,zebra,_,_,_],H).





