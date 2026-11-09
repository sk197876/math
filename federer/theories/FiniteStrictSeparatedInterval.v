(** Federer (1969), 3.3.19, p. 306: strict
    finite tangential packing for the original children
    in the final upper-density estimate. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality lra.
From Federer Require Import FiniteRealMaximum FiniteSeparatedRealInterval FiniteTwoDistinctMembers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Packing.
Variable R:realType.

(** Source for [finite_strict_separated_interval_bound]: a
    finite set of at least two points, strictly q separated
    in [a,b], satisfies card(F)q<b-a+q. A local actual
    smallest pair distance strengthens the already proved weak
    packing bound. This supports 3.3.19, p. 306. *)
Theorem finite_strict_separated_interval_bound (F:{fset R}) (a b q:R):
  (2<=#|` F|)%N ->0<q ->a<=b ->
  (forall x,x \in F ->a<=x /\x<=b) ->
  (forall x y,x \in F ->y \in F ->x!=y ->q<`|x-y|) ->
  #|` F|%:R* q<b-a+q.
Proof.
move=>hCount hq hab hBounds hSeparate.
pose I:=[the finType of (F* F)%type].
pose G:set I:=[set xy|val xy.1!=val xy.2].
have [x [y [hx [hy hxy]]]]:= @finite_two_distinct_members R F hCount.
have hGNonempty:G!=set0.
  exists ((Sub x hx),(Sub y hy));exact:hxy.
have hGFinite:finite_set G:= finite_finset.
have [uv [hUV hMinimum]]:= @finite_nonempty_real_maximum R I G
  (fun xy:I=> -`|val xy.1-val xy.2|) hGFinite hGNonempty.
pose d:=`|val uv.1-val uv.2|.
have hqd:q<d:= hSeparate (val uv.1) (val uv.2) (fsvalP uv.1) (fsvalP uv.2) hUV.
have hd:0<d:= lt_trans hq hqd.
have hWeak x0 y0:x0 \in F ->y0 \in F ->x0!=y0 ->d<=`|x0-y0|.
  move=>hx0 hy0 hDifferent.
  have hPair:G ((Sub x0 hx0),(Sub y0 hy0)):= hDifferent.
  have h:= hMinimum _ hPair.
  by rewrite lerN2 in h.
have hBound:= @finite_separated_real_interval_bound R F a b d hd hab hBounds hWeak.
have hN:1<(#|` F|%:R:R) by rewrite ltr1n.
have hScaled:(#|` F|%:R-1)* q<(#|` F|%:R-1)* d by rewrite ltr_pM2l //;lra.
nra.
Qed.
End Packing.
