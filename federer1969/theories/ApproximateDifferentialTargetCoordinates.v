(** Federer (1969), 3.1.4, p. 214: reduction to the scalar
    target. Approximate differentials of finitely many coordinates
    combine into the prescribed vector differential, including an
    empty target coordinate family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric InnerNormedTopology HilbertFormCompactness EuclideanLebesgueDimensions
  EuclideanLebesgueHaar EuclideanApproximateContext EuclideanFiniteZeroDensity
  CenteredBallRelations PartialFunctionUP MeasureSetDensity LocalZeroDensity
  ApproximateDifferentialUP ApproximateDifferentialIncrementCriterion
  ApproximateDifferentialIncrementDensity RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_differential_from_target_coordinates]:
    the scalar reduction in the proof of Federer 3.1.4, p. 214.
    The candidate map is abstractly specified by its coordinate maps;
    a finite union controls all coordinate errors. Positive source
    dimension retains the punctured-quotient convention of 3.1.2. *)
Theorem approximate_differential_from_target_coordinates (R : realType) m n
    (f : R_n R m.+1 -> R_n R n) (a : R_n R m.+1)
    (L : Hom (R_n R m.+1) (R_n R n))
    (Lc : 'I_n -> Hom (R_n R m.+1) [the lmodType R of R^o]) :
  (forall j h, Lc j h=(L h) j) ->
  (forall j, has_approximate_differential (fun z : R^o=>`|z|) setT
    (fun x=>f x j) a (Lc j)) ->
  has_approximate_differential (inner_norm (@euclidean_inner_productP R n)) setT f a L.
Proof.
move=> hLc hc.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose NX := inner_norm (@euclidean_inner_productP R m.+1).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose V := @centered_closed_ball_relation R [the metricType R of X].
apply: (approximate_differential_increment_density_criterion
  (inner_norm_real_norm (@euclidean_inner_productP R n)))=> e he.
pose d := e/n.+1%:R.
have hn : 0<(n.+1%:R : R) by rewrite ltr0n.
have hd : 0<d by rewrite /d divr_gt0.
pose N j : set X := [set h | d*NX h<`|f (a+h) j-f a j-Lc j h|].
have hN (j : 'I_n) : partial_function_graph (measure_set_density mu V (N j)) 0 0%E.
  exact: (approximate_differential_increment_density_zero (scalar_absolute_value_norm R) (hc j) hd).
have hU := euclidean_finite_union_density_zero hN.
apply: (@local_zero_density_mono R [the metricType R of X] mu V _
  (\bigcup_j N j) setT 0 (euclidean_approximate_context R m.+1) openT Logic.I _ hU)=> h _ hh.
apply: contrapT=> hall.
have hcoords (j : 'I_n) : `|(f (a+h)-f a-L h) j|<=d*NX h.
  rewrite !ffunE -hLc leNgt; apply/negP=> hj; apply: hall; by exists j.
have hb : NY (f (a+h)-f a-L h)<=n%:R*(d*NX h).
  rewrite /NY -inner_norm_topologyE.
  apply: le_trans (euclidean_norm_coordinate_sum (f (a+h)-f a-L h)) _.
  apply: le_trans (_ : \sum_(j<n) `|(f (a+h)-f a-L h) j|<=\sum_(j<n) (d*NX h)) _.
  - apply: ler_sum=> j _; exact: hcoords.
  - by rewrite sumr_const card_ord -[(_ *+ n)]mulr_natl.
have hcoef : n%:R*d<=e.
  have hid : n.+1%:R*d=e by rewrite /d mulrC mulfVK ?(gt_eqF hn).
  rewrite -hid; apply: ler_wpM2r; first exact: ltW hd.
  by rewrite ler_nat leqnSn.
have hb' : NY (f (a+h)-f a-L h)<=e*NX h.
  apply: le_trans hb _; rewrite mulrA.
  apply: ler_wpM2r; first exact: inner_norm_nonnegative.
  exact hcoef.
by have := le_lt_trans hb' hh; rewrite ltxx.
Qed.
