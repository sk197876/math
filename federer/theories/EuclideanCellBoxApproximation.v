(** Federer (1969), 4.1.23, p. 379:
    retain the literal compact box closures
    when the earlier Lebesgue approximation is
    used on the original current norm topology.
    Both Euclidean metric interfaces are related
    by the already proved continuous identity maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm InnerMetric
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanDistributionMeasureContext EuclideanLebesgueDimensions
  EuclideanOpenCoordinateBoxUP FiniteDisjointOpenBoxFamilyUP
  MeasurableCellBoxApproximation ClosedCoordinateBoxConvex ClosedCoordinateBoxGeometry
  MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_inner_norm_closure]:
    the literal closed box used
    in Federer 4.1.23, pp. 379–380,
    is independent of the equivalent
    inner-product and own-norm metric interfaces.
    This identifies closures of the same
    actual subset, not different current topologies. *)
Lemma euclidean_inner_norm_closure (R : realType) n (A : set (R_n R n)) :
  @closure (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) A=
    @closure (inner_metric_space (@euclidean_inner_productP R n)) A.
Proof.
apply: funext=> x; apply: propext; split=> hx W hW.
- apply: hx.
  exact: (@euclidean_distribution_norm_to_inner R n x W hW).
- apply: hx.
  exact: (@euclidean_distribution_inner_to_norm R n x W hW).
Qed.

(** Source for [euclidean_cell_box_approximation]:
    the suitable rectangular approximation
    in Federer 4.1.23, p. 379,
    keeps each entire closed coordinate
    box inside the prescribed open W.
    The original measurable cell has any
    compact carrier; empty and null cells
    and ambient dimension zero are retained. *)
Theorem euclidean_cell_box_approximation (R : realType) n
    (A K W : set (R_n R n)) (epsilon : R) :
  let NT := real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)) in
  measure_measurable (@euclidean_lebesgue_measure R n) A ->
  @compact NT K -> A `<=` K -> @open NT W -> K `<=` W -> 0<epsilon ->
  exists (I : finType) (a b : I -> R_n R n) (G : I -> set (R_n R n)),
    is_finite_disjoint_open_box_family a b G /\
    (forall i, @closed_coordinate_box R n (a i) (b i) `<=` W) /\
    (@euclidean_lebesgue_measure R n (A `\` (\bigcup_i G i))+
      @euclidean_lebesgue_measure R n ((\bigcup_i G i) `\` A)<epsilon%:E)%E /\
    (@euclidean_lebesgue_measure R n (\bigcup_i G i)<=
      @euclidean_lebesgue_measure R n A+epsilon%:E)%E.
Proof.
move=> NT hA hK hAK hW hKW hEpsilon.
pose IT := inner_metric_space (@euclidean_inner_productP R n).
have hKInner : @compact IT K.
  have hImage := continuous_compact
    (continuous_subspaceT (@euclidean_distribution_norm_to_inner R n)) hK.
  change (@compact IT ((fun x : NT => (x:IT)) @` K)) in hImage.
  by rewrite image_id in hImage.
have hWInner : @open IT W.
  exact: ((@continuousP IT NT (fun x => x)).1
    (@euclidean_distribution_inner_to_norm R n) W hW).
have [I [a [b [G [hFamily [hClosures [hError hMass]]]]]]] :=
  @measurable_cell_box_approximation R n A K W epsilon hA hKInner hAK hWInner hKW hEpsilon.
have hClosedBoxes i : @closed_coordinate_box R n (a i) (b i) `<=` W.
  move=> x hx; apply: (@hClosures i x).
  rewrite -euclidean_inner_norm_closure
    (@proper_coordinate_box_closure R n (a i) (b i) (G i)
      (@finite_disjoint_open_box_law R n I a b G hFamily i)).
  exact: hx.
exists I,a,b,G; split; first exact: hFamily.
split; first exact: hClosedBoxes.
by split.
Qed.
