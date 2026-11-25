(** Federer (1969), 3.1.4, p. 214: joint measurability of
    the remainder-exception set whose radius sections are T(x,r,i,j).
    The scalar tolerance is arbitrary; the printed choice is 1/j. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanOneCoordinate EuclideanLebesgueDimensions RealMetricBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialFunctionPair
  PartialFunctionPrecomposition MeasureUP ProductMeasure ProductFunctionMeasurability
  MeasurableFunctionUP MeasurableRealArithmetic CoordinateDifferenceQuotient
  CoordinateDifferenceQuotientMeasurable MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section RemainderSets.
Variable R : realType.
Variable m : nat.
Variable i : 'I_m.
Variables f g : R_n R m -> R^o.
Variable e : R.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation T := (inner_metric_space (@euclidean_inner_productP R 1)).

(** Source for [coordinate_remainder_exception_set]: the
    inequality defining T in Federer 3.1.4, p. 214. Its
    intersection with a radius ball is the exceptional scalar section. *)
Definition coordinate_remainder_exception_set : set (X*T) :=
  [set xt | e*`|euclidean_one_project xt.2|<
    `|f (xt.1+euclidean_one_project xt.2*:(@coordinate_basis R m i))-
      f xt.1-euclidean_one_project xt.2*g xt.1|].

(** Source for [coordinate_remainder_exception_measurable]:
    the measurability needed to apply 3.1.3(1) to B(i,j,p)
    in Federer 3.1.4, pp. 214–215. The quotient is used only
    away from zero, and the remainder inequality is false at zero. *)
Theorem coordinate_remainder_exception_measurable :
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total f) ->
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (partial_function_total g) ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R 1)) coordinate_remainder_exception_set.
Proof.
move=> hf hg.
pose ha := euclidean_lebesgue_is_measure R m.
pose hb := euclidean_lebesgue_is_measure R 1.
pose mu := product_measure ha hb.
pose hm := product_measure_is_measure ha hb.
pose Q := euclidean_joint_coordinate_quotient i (partial_function_total f).
pose G := partial_function_total (fun xt : X*T=>(g xt.1 : real_line_metric R)).
pose H := partial_real_function_subtract Q G.
have hQ := euclidean_joint_coordinate_quotient_measurable i hf.
have hG := product_measurable_first_function ha hb hg.
have hH := @measurable_real_function_subtract R [the choiceType of (X*T)%type] mu hm Q G hQ hG.
pose U := [set z : real_line_metric R | e<`|z|].
have hU : open U.
  have he : U=~` metric_closed_ball (0 : real_line_metric R) e.
    apply/seteqP; split=> z; change ((e<`|z|)->~(mdist (0 : real_line_metric R) z<=e)) ||
      change (~(mdist (0 : real_line_metric R) z<=e)->(e<`|z|));
      rewrite real_line_metric_distanceE sub0r normrN ltNge; by move/negP.
  rewrite he; apply: closed_openC; exact: metric_closed_ball_closed.
have hid : coordinate_remainder_exception_set=partial_function_preimage H U.
  apply/seteqP; split; move=> [x t] hx.
  - have ht : euclidean_one_project t!=0.
      by apply/eqP=> ht; move: hx; rewrite /coordinate_remainder_exception_set /= ht normr0 mulr0
        scale0r addr0 mul0r subrr subr0 normr0 ltxx.
    pose z := (euclidean_one_project t)^-1*(f (x+euclidean_one_project t*:(@coordinate_basis R m i))-f x).
    exists (z-g x); split.
    + exists (z,g x); split=> //; split=> //.
      apply: (euclidean_joint_coordinate_quotient_graph i (partial_function_total f) x t z).2.
      split=> //; exists (f (x+euclidean_one_project t*:(@coordinate_basis R m i))),(f x).
      by split=> //; split.
    + have heq : f (x+euclidean_one_project t*:(@coordinate_basis R m i))-f x-
          euclidean_one_project t*g x=euclidean_one_project t*(z-g x).
        by rewrite /z mulrBr mulrA mulfV // mul1r.
      move: hx; rewrite /coordinate_remainder_exception_set /= heq normrM mulrC.
      by rewrite ltr_pM2l ?normr_gt0.
  - move: hx=> [z [[[q b] [[hq hb0] hz]] hu]].
    have [ht [u [v [hfu [hfv hqv]]]]] :=
      (euclidean_joint_coordinate_quotient_graph i (partial_function_total f) x t q).1 hq.
    change (g x=b) in hb0.
    change (f (x+euclidean_one_project t*:(@coordinate_basis R m i))=u) in hfu.
    change (f x=v) in hfv.
    change (q-b=z) in hz.
    have heq : f (x+euclidean_one_project t*:(@coordinate_basis R m i))-f x-
        euclidean_one_project t*g x=euclidean_one_project t*z.
      by rewrite -hz -hb0 hqv -hfu -hfv mulrBr mulrA mulfV // mul1r.
    rewrite /coordinate_remainder_exception_set /= heq normrM mulrC.
    by rewrite ltr_pM2l ?normr_gt0.
rewrite hid; exact (@measurable_function_open_preimage R [the choiceType of (X*T)%type]
  [the topologicalType of real_line_metric R] mu H hH U hU).
Qed.
End RemainderSets.
