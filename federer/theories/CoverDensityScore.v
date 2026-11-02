(** Federer (1969), 2.5.7, p. 99: tau for q=infinity is the dyadic sum of
    normalized integrals over finite-measure sets covering X. These are
    actual integral coordinates, not arbitrary assumed scores. Strictness
    follows from equality in integral order and a common conull set for the
    countable cover. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic TotalScalarLpUP
  FiniteSetDensityAverage DyadicAverageScore.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cover_density_score]: direct case-(ii) formula for tau in
    Federer 2.5.7, p. 99 Natural indices begin at zero, so the weights are
    2^(-n-1), preserving the printed series. *)
Definition cover_density_score (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (F : nat -> set X) (u : X -> R) :=
  dyadic_average_score (fun n => finite_set_density_average mu (F n) u).

(** Source for [cover_density_score_bounds]: the range [0,M] of tau in
    Federer 2.5.7, p. 99 Every coordinate bound is proved from the
    L-infinity norm and the finite covering mass. *)
Lemma cover_density_score_bounds (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : nat -> set X) (u : X -> R) (M : R) :
  (forall n, measure_measurable mu (F n) /\ 0 < mu (F n) < +oo) ->
  (0 <= M)%R -> total_scalar_lp mu +oo u -> (forall x, (0 <= u x)%R) ->
  total_scalar_lp_norm mu +oo u <= M%:E -> (0 <= cover_density_score mu F u <= M)%R.
Proof.
move=> hF hM hu hu0 hb; apply: (@dyadic_average_score_bounds R _ M hM)=> n.
exact: (@finite_set_density_average_bounds R X mu hm (F n) u M (hF n).1 (hF n).2 hu hu0 hb).
Qed.

(** Source for [cover_density_score_almost_order]: the increasing property
    of tau in Federer 2.5.7, p. 99 Exceptional null sets are allowed in the
    order between the densities. *)
Lemma cover_density_score_almost_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : nat -> set X) (u v : X -> R) (M : R) :
  (forall n, measure_measurable mu (F n) /\ 0 < mu (F n) < +oo) ->
  (0 <= M)%R -> total_scalar_lp mu +oo u -> total_scalar_lp mu +oo v ->
  (forall x, (0 <= u x)%R) -> (forall x, (0 <= v x)%R) ->
  total_scalar_lp_norm mu +oo u <= M%:E -> total_scalar_lp_norm mu +oo v <= M%:E ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  (cover_density_score mu F u <= cover_density_score mu F v)%R.
Proof.
move=> hF hM hu hv hu0 hv0 hbu hbv huv.
apply: (@dyadic_average_score_monotone R _ _ M hM).
- move=> n; exact: (@finite_set_density_average_bounds R X mu hm (F n) u M (hF n).1 (hF n).2 hu hu0 hbu).
- move=> n; exact: (@finite_set_density_average_bounds R X mu hm (F n) v M (hF n).1 (hF n).2 hv hv0 hbv).
- move=> n; exact: (@finite_set_density_average_almost_order R X mu hm (F n) u v (hF n).1 (hF n).2 hu hv huv).
Qed.

(** Source for [cover_density_score_strict_order]: strict increase of tau
    under Federer's almost order, 2.5.7, p. 99 A positive-measure strict
    locus forces a strict inequality in at least one coordinate, because
    otherwise the covering-set equality laws imply almost equality. *)
Theorem cover_density_score_strict_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : nat -> set X) (u v : X -> R) (M : R) :
  setT=\bigcup_n F n ->
  (forall n, measure_measurable mu (F n) /\ 0 < mu (F n) < +oo) ->
  (0 <= M)%R -> total_scalar_lp mu +oo u -> total_scalar_lp mu +oo v ->
  (forall x, (0 <= u x)%R) -> (forall x, (0 <= v x)%R) ->
  total_scalar_lp_norm mu +oo u <= M%:E -> total_scalar_lp_norm mu +oo v <= M%:E ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  0 < mu [set x | (u x < v x)%R] ->
  (cover_density_score mu F u < cover_density_score mu F v)%R.
Proof.
move=> hcover hF hM hu hv hu0 hv0 hbu hbv huv hpos.
have hle n := @finite_set_density_average_almost_order R X mu hm (F n) u v (hF n).1 (hF n).2 hu hv huv.
have hex : exists j, (finite_set_density_average mu (F j) u < finite_set_density_average mu (F j) v)%R.
  apply: contrapT=> hnone.
  have he n : finite_set_density_average mu (F n) u=finite_set_density_average mu (F n) v.
    apply/eqP; rewrite eq_le (hle n) andTb leNgt; apply/negP=> hn.
    apply: hnone; by exists n.
  have heA n := @finite_set_density_average_equality R X mu hm (F n) u v (hF n).1 (hF n).2 hu hv huv (he n).
  have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT
    (fun n => [set x | F n x -> u x=v x]) (countableP setT) (fun n _ => heA n).
  have heq : measure_almost_everywhere mu [set x | u x=v x].
    apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hall)=> x hx.
    have hxF : (\bigcup_n F n) x by rewrite -hcover.
    have [n _ hn] := hxF; exact: hx n I hn.
  have hz : mu [set x | (u x < v x)%R]=0.
    apply: (@measure_null_subset R X mu hm _ _ _ heq)=> x hx heuv.
    change (is_true (u x < v x)%R) in hx; by rewrite heuv ltxx in hx.
  by rewrite hz ltxx in hpos.
have [j hj] := hex.
apply: (@dyadic_average_score_strict R _ _ M j hM).
- move=> n; exact: (@finite_set_density_average_bounds R X mu hm (F n) u M (hF n).1 (hF n).2 hu hu0 hbu).
- move=> n; exact: (@finite_set_density_average_bounds R X mu hm (F n) v M (hF n).1 (hF n).2 hv hv0 hbv).
- exact: hle.
- exact: hj.
Qed.
