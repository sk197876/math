(** Federer (1969), 3.3.19, p. 304:
    joining finitely many actual curve points in
    parameter order gives a closed polygon whose
    length is at most the original curve variation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import CurveVariationUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_curve_ordered_polygon_bound]:
    the final cyclic-length comparison of 3.3.19,
    p. 304, at the level of an actual
    closed curve. Insert the original two endpoints
    into the ordered list; the metric triangle
    inequality controls the closing chord. *)
Lemma closed_curve_ordered_polygon_bound (R:realType) (Y:metricType R)
    (g:R->Y) (a b:R) (u:R) (s:seq R):
  sorted <=%O (u::s) ->
  (forall x,x \in u::s ->a<=x /\x<=b) ->g a=g b ->
  ((chain_sum g (u::s)+mdist (g (last u s)) (g u))%:E<=curve_variation g a b)%E.
Proof.
move=>hSorted hBounds hEnds.
pose P:=a::(u::s)++[::b].
have hBefore:sorted <=%O (a::u::s).
  change (is_true (sorted <=%O ([::a]++u::s))).
  apply:(@sorted_cat_le R [::a] (u::s)).
  - by [].
  - exact hSorted.
  - move=>x y;rewrite inE=>/eqP -> hy;exact:(hBounds y hy).1.
have hP:sorted <=%O P.
  change (is_true (sorted <=%O ((a::u::s)++[::b]))).
  apply:(@sorted_cat_le R (a::u::s) [::b]).
  - exact hBefore.
  - by [].
  - move=>x y;rewrite !inE=>/orP[/eqP->|hx] /eqP->.
    + exact:(le_trans (hBounds u (mem_head u s)).1 (hBounds u (mem_head u s)).2).
    + exact:(hBounds x hx).2.
have hPartition:is_variation_partition a b P.
  split=>//;split.
  - by rewrite /P /= size_cat /= !ltnS addn1.
  - split;first exact:erefl;by rewrite /P last_cons last_cat /=.
have hVar:((chain_sum g P)%:E<=curve_variation g a b)%E.
  apply:extended_real_sup_upper;exists P;by split.
have hSum:chain_sum g P=
    mdist (g a) (g u)+chain_sum g (u::s)+mdist (g (last u s)) (g b).
  rewrite /P -cat_cons cats1 chain_sum_rcons;last by [].
  by rewrite chain_sum_cons /=.
have hTriangle:=metric_triangle (g (last u s)) (g b) (g u).
have hSame:mdist (g b) (g u)=mdist (g a) (g u) by rewrite hEnds.
rewrite hSame in hTriangle.
apply:(le_trans _ hVar);rewrite lee_fin hSum;lra.
Qed.
