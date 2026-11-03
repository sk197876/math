(** Federer (1969), 3.2.40, p. 276: supporting
    finite indexed point packings in the actual Euclidean
    tube, with disjoint positive-radius balls. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology lra
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology
  EuclideanLebesgueDimensions EuclideanBallVolume MetricOpenThickening MetricClosedBalls
  MeasureUP MeasureBasic FiniteNullOverlapAdditivity FiniteCoverMeasureBounds
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory
  numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_indexed_separated_tube_volume]: supporting
    point-packing volume estimate in Federer 3.2.40, p. 276.
    Distinct indices have centres separated by at least 2r,
    so their actual open r-balls are disjoint. Finite measure
    additivity gives the exact volume, even for an empty
    index family and ambient dimension zero. *)
Theorem finite_indexed_separated_tube_volume (R:realType) n (I:finType)
    (a:I->inner_metric_space (@euclidean_inner_productP R n)) (r:R):
  (0<r)%R ->(forall i j,i!=j ->(2*r<=mdist (a i) (a j))%R) ->
  @euclidean_lebesgue_measure R n (metric_open_thickening (a @` setT) r)=
    (#|I|%:R*(euclidean_unit_ball_volume R n*r^+n))%R%:E.
Proof.
move=>hr hSeparated.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
pose F (i:I):=[set x:X|(mdist (a i) x<r)%R].
have hMeas i:measure_measurable mu (F i).
  apply:(@borel_regular_borel_measurable R X mu hm (euclidean_lebesgue_borel_regular R n)).
  exact:open_borel_set (metric_open_ball_open (a i) r).
have hNull i j:i!=j ->mu (F i `&` F j)=0.
  move=>hDifferent.
  have hEmpty:F i `&` F j=set0.
    apply/seteqP; split=>[x [hix hjx]|x hx]; last by [].
    have hLower:=hSeparated i j hDifferent.
    have hTriangle:=metric_triangle (a i) x (a j).
    rewrite (metric_sym x (a j)) in hTriangle.
    change (is_true (mdist (a i) x<r)%R) in hix.
    change (is_true (mdist (a j) x<r)%R) in hjx.
    have hBad:(2*r<2*r)%R by lra.
    by rewrite ltxx in hBad.
  exact:(eq_trans (congr1 mu hEmpty) (@measure_empty R X mu hm)).
have hUnion:metric_open_thickening (a @` setT) r=\bigcup_i F i.
  apply/seteqP; split.
  - move=>x [y [i _ <-] hDistance]; by exists i.
  - move=>x [i _ hDistance]; exists (a i); last exact hDistance.
    by exists i.
have hAdd:=@measure_finite_family_null_overlap_additivity R X I mu hm F setT
  (@finite_finset I setT) (fun i _=>hMeas i) (fun i j _ _=>hNull i j).
rewrite (@finite_type_nonnegative_sum R I (fun i=>mu (F i))
  (fun i=>measure_nonnegative hm (F i))) in hAdd.
have hVolume i:mu (F i)=(euclidean_unit_ball_volume R n*r^+n)%R%:E.
  have hF:F i=[set x:X|(`|x-a i|<r)%R].
    apply/seteqP; split=>x.
    - change ((mdist (a i) x<r)%R ->(`|x-a i|<r)%R).
      by rewrite inner_metric_normE.
    - change ((`|x-a i|<r)%R ->(mdist (a i) x<r)%R).
      by rewrite inner_metric_normE.
  rewrite hF; exact:euclidean_ball_measure hr.
rewrite /mu in hAdd hVolume.
rewrite hUnion hAdd (eq_bigr _ (fun i _=>hVolume i)) sumEFin sumr_const cardT.
by rewrite (mulr_natl (euclidean_unit_ball_volume R n*r^+n)%R (size (enum I))).
Qed.
