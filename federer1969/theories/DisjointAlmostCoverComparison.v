(** Summation over the disjoint geometric levels in Federer (1969), 2.9.7,
    p. 156. A countable disjoint almost cover transfers a cellwise
    comparison to the target's mass. Additivity, nonnegative summation and
    scalar factoring are the already proved laws 2.1.1(6) and 2.1.3(3), pp.
    52, 55. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureCountableAdditivity MeasureDisjointSupport
  NonnegativeSum NonnegativeSumScale VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_disjoint_almost_cover_comparison]:
    supporting sum comparison in Federer 2.9.7, p. 156.
    The covering remainder is null for the first
    measure. Measurable disjoint cells lie inside A;
    A itself need not be measurable and totals may
    be infinite. *)
Lemma measure_disjoint_almost_cover_comparison (R : realType) (X J : choiceType)
    (mu nu : set X -> \bar R) (A : set X) (D : set J) (F : J -> set X) (t : R) :
  is_measure mu -> is_measure nu -> (0<=t)%R -> countable D ->
  (forall j, D j -> F j `<=` A) ->
  (forall j, D j -> measure_measurable mu (F j)) ->
  (forall j, D j -> measure_measurable nu (F j)) ->
  (forall j k, D j -> D k -> j<>k -> F j `&` F k=set0) ->
  mu (A `\` \bigcup_(j in D) F j)=0 ->
  (forall j, D j -> mu (F j)<=t%:E*nu (F j)) -> mu A<=t%:E*nu A.
Proof.
move=> hm hn ht hD hFA hFm hFn hdis hz hcell.
have hcover := @null_remainder_measure_cover_bound R X mu A (\bigcup_(j in D) F j) hm hz.
have hd j k : D j -> D k -> j!=k -> forall x, F j x -> F k x -> False.
  move=> hj hk /eqP hne x hx hy; have hxy : (F j `&` F k) x by split.
  by rewrite (hdis j k hj hk hne) in hxy.
have he := @measure_countable_disjoint_additivity R X J mu hm D F hD hFm hd.
have hsum : nonnegative_sum D (fun j => mu (F j))<=nonnegative_sum D (fun j => t%:E*nu (F j)).
  exact: nonnegative_sum_mono hcell.
have hscale := @nonnegative_sum_scale R J D (fun j => nu (F j)) t ht
  (fun j _ => measure_nonnegative hn _).
have hbound := @measure_disjoint_sum_bound R X J nu hn A D F hFA hFn hdis.
have htE : 0<=t%:E by rewrite lee_fin.
have hmul := @lee_wpmul2l R t%:E htE _ _ hbound.
rewrite he in hcover; rewrite hscale in hsum.
exact: le_trans hcover (le_trans hsum hmul).
Qed.
