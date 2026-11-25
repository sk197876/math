(** Finite positive-ball covers in the project test of the spherical
    parenthesis in Federer 2.10.11, p. 176. The source spherical
    length is at most one, using only existing cylinder counting. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import BinarySequenceCylinders BinaryCylinderPrefixLaws
  BinaryCylinderCost BinaryCylinderRefinementCost BinaryPrefixMetric BinaryPrefixBalls
  DyadicScaleBounds MetricClosedBalls MetricDiameter HausdorffMeasureUP
  HausdorffMeasure HausdorffDiameterCost CaratheodoryLimitUP CaratheodoryBorelRegular
  MetricScaleEnvelopeUP MetricScaleIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_prefix_spherical_length_upper]: an actual
    finite spherical mass bound in the project example testing
    Federer 2.10.11, p. 176. Length-n cylinders are positive closed
    balls with diameter at most 2^(-n); their total cost is one. *)
Theorem binary_prefix_spherical_length_upper (R:realType):
  @spherical_measure R (binary_prefix_metric R) 1 setT<= 1.
Proof.
apply:(caratheodory_limit_least
  (@spherical_measure_specification R (binary_prefix_metric R) 1))=>delta nu hd hn.
have [ell hell]:=reciprocal_metric_cutoffs_cofinal hd.
have hpos:(0<(ell.+1%:R:R)^-1)%R by rewrite invr_gt0 ltr0n.
have [n hsmall]:=dyadic_sides_arbitrarily_small hpos.
have hball (w:n.-tuple bool):
    @is_positive_metric_closed_ball R (binary_prefix_metric R) (binary_cylinder w).
  rewrite (@binary_prefix_cylinder_ball R w).
  exact:positive_closed_ball_satisfies_laws (dyadic_side_positive R (size w)).
pose u (w:n.-tuple bool):@positive_closed_metric_balls R (binary_prefix_metric R):=
  Sub (binary_cylinder w) (mem_set (hball w)).
have hdiam w:extended_metric_diameter (val (u w))<=delta.
  apply:le_trans (binary_prefix_cylinder_diameter_bound R w) _.
  rewrite size_tuple;apply:le_trans _ hell;rewrite lee_fin;exact:ltW hsmall.
have hcov:setT `<=` \bigcup_(w in (@setT (n.-tuple bool))) val (u w).
  move=> x _;exists (binary_sequence_prefix n x)=> //.
  exact:@binary_sequence_in_prefix n x.
have hcost w:hausdorff_diameter_cost 1 (val (u w))<=binary_cylinder_cost R w.
  rewrite hausdorff_diameter_cost_one_degree.
  apply:le_trans (binary_prefix_cylinder_diameter_bound R w) _.
  by rewrite /binary_cylinder_cost size_tuple natrX.
have h:=@metric_scale_envelope_indexed_cover R (binary_prefix_metric R)
  _ [the choiceType of n.-tuple bool] (fun j=>val j)
  (fun j=>hausdorff_diameter_cost 1 (val j)) delta nu hn setT setT u
  (@countableP [the countType of n.-tuple bool] setT) (fun w _=>hausdorff_diameter_cost_nonnegative 1 (val (u w)))
  (fun w _=>hdiam w) hcov.
apply:le_trans h _;apply:le_trans (nonnegative_sum_mono (fun w _=>hcost w)) _.
have hsum:=@binary_cylinder_refinement_sum R n [::] (leq0n n).
have he:[set w:n.-tuple bool|prefix [::] w]=setT.
  apply/seteqP;split;first by move=> w _.
  move=> w _;change (is_true (prefix [::] w));exact:prefix0s.
by rewrite he binary_cylinder_cost_empty_word in hsum;rewrite hsum.
Qed.
