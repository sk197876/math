(** Federer (1969), 3.1.4, pp. 215–216: the finite union of
    controlled coordinate exceptions gives the approximate differential
    whose standard-basis values are the approximate partial derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric RealNormUP RealMetricBackground EuclideanCoordinateTopology
  EuclideanLebesgueDimensions MetricClosedBalls MeasureUP MeasureBasic
  MeasureFiniteUnionBound ApproximateDifferentialUP
  ApproximateCoordinateExceptionalSets ApproximateDifferentialUniformMassCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_coordinate_mass_criterion]: the union
    bound and final limiting argument of Federer 3.1.4, p. 216.
    The separate section calculation on p. 215 supplies the premise
    with C=2^(m+1). It is a supporting criterion, not the final
    almost-everywhere theorem. *)
Theorem approximate_coordinate_mass_criterion (R : realType) n
    (f : R_n R n.+1 -> R^o) (g : 'I_n.+1 -> R_n R n.+1 -> R^o)
    (a : R_n R n.+1) (L : Hom (R_n R n.+1) [the lmodType R of R^o]) (C : R) :
  (forall i, L (@coordinate_basis R n.+1 i)=g i a) -> 0<=C ->
  (forall j : nat, exists d : R, 0<d /\ forall r : R, 0<r -> r<d ->
    forall i : 'I_n.+1,
    (euclidean_lebesgue_measure n.+1
      (coordinate_staircase_exception f g a (j.+1%:R)^-1 i `&`
        metric_closed_ball (0%R : inner_metric_space (@euclidean_inner_productP R n.+1)) r)
      <=(C*(j.+1%:R)^-1*r^+n.+1)%R%:E)%E) ->
  has_approximate_differential (fun x : R^o=>`|x|) setT f a L.
Proof.
move=> hL hC hs.
have hLe h : L h=\sum_(i<n.+1) h i*g i a.
  rewrite -{1}(euclidean_coordinate_expansion h) linear_sum.
  by apply: eq_bigr=> i _; rewrite linearZ /= hL.
apply: (@approximate_differential_uniform_mass_criterion R n [the lmodType R of R^o]
  (fun x=>`|x|) (scalar_absolute_value_norm R) f a L (2*n.+1%:R) (n.+1%:R*C)).
- by rewrite mulr_ge0 // ler0n.
- by rewrite mulr_ge0 // ler0n.
- move=> j; have [d [hd hb]] := hs j; exists d; split=> // r hr hrd.
  pose X := inner_metric_space (@euclidean_inner_productP R n.+1).
  pose S i := coordinate_staircase_exception f g a (j.+1%:R)^-1 i `&`
    metric_closed_ball (0 : X) r.
  have hcov : [set h : X | (2*n.+1%:R*(j.+1%:R)^-1)*
      inner_norm (@euclidean_inner_productP R n.+1) h < `|f (a+h)-f a-L h|] `&`
      metric_closed_ball (0 : X) r `<=` \bigcup_i S i.
    move=> h [hh hball].
    rewrite /= hLe in hh.
    have he : 0<=(j.+1%:R : R)^-1 by rewrite invr_ge0 ler0n.
    have [i _ hi] := coordinate_staircase_remainder_exception_cover he hh.
    exists i=> //; by split.
  apply: le_trans (measure_mono (euclidean_lebesgue_is_measure R n.+1) hcov) _.
  apply: le_trans (measure_finite_union_bound S (euclidean_lebesgue_is_measure R n.+1)) _.
  apply: le_trans (_ : (\sum_(i<n.+1) euclidean_lebesgue_measure n.+1 (S i)<=
    \sum_(i<n.+1) (C*(j.+1%:R)^-1*r^+n.+1)%R%:E)%E) _.
  - apply: lee_sum=> i _; exact: hb r hr hrd i.
  - rewrite sumEFin sumr_const card_ord lee_fin -[(_ *+ n.+1)]mulr_natr.
    have hid : (C*(j.+1%:R)^-1*r^+n.+1)*n.+1%:R=
        n.+1%:R*C*(j.+1%:R)^-1*r^+n.+1 by ring.
    by rewrite hid.
Qed.
