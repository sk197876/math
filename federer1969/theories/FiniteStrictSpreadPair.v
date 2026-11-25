(** Federer (1969), 3.3.19, p. 306: three
    strictly separated tangential coordinates have two
    extremes separated by more than twice the spacing. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality lra.
From Federer Require Import FiniteRealMaximum FiniteStrictSeparatedInterval FiniteTwoDistinctMembers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Spread.
Variable R:realType.

(** Source for [finite_strict_spread_pair]: a finite
    family of at least three q-separated real points
    has actual minimum and maximum at distance >2q.
    The local witnesses and strict finite packing supply
    the extreme pair in the last density proof of
    3.3.19, p. 306. *)
Theorem finite_strict_spread_pair (F:{fset R}) (q:R):
  (3<=#|` F|)%N ->0<q ->
  (forall x y,x \in F ->y \in F ->x!=y ->q<`|x-y|) ->
  exists x y:R,x \in F /\y \in F /\2* q<y-x.
Proof.
move=>hCount hq hSeparate.
have hTwo:(2<=#|` F|)%N:= leq_trans (erefl true:(2<=3)%N) hCount.
have [a [_ [ha _]]]:= @finite_two_distinct_members R F hTwo.
have hNonempty:[set` F]!=set0 by exists a.
have hFinite:finite_set [set` F] by apply/finite_fsetP;by exists F.
have [x [hx hMinimum]]:= @finite_nonempty_real_maximum R R [set` F] (fun t:R=> -t) hFinite hNonempty.
have [y [hy hMaximum]]:= @finite_nonempty_real_maximum R R [set` F] (fun t:R=>t) hFinite hNonempty.
have hMinimumOrd t:t \in F ->x<=t.
  move=>ht;have h:= hMinimum t ht;by rewrite lerN2 in h.
have hBounds t:t \in F ->x<=t /\t<=y by move=>ht;split;[exact:hMinimumOrd t ht|exact:hMaximum t ht].
have hXY:x<=y:= hMinimumOrd y hy.
have hStrict:= @finite_strict_separated_interval_bound R F x y q hTwo hq hXY hBounds hSeparate.
have hN3:(3<=#|` F|%:R:>R) by rewrite ler_nat.
exists x,y;split=>//;split=>//;nra.
Qed.
End Spread.
