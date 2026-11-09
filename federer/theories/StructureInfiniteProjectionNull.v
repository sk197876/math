(** Federer (1969), 3.3.9, pp. 295–296: complete original
    projected nullity from infinite upper cone growth. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructurePlaneGrowth StructureProjectionKernel StructureFiniteProjectionRegularisation
  StructureInfiniteConeProjectionGrowth EuclideanLebesgueDimensions EuclideanApproximateContext
  MeasureDerivationContext MeasureUP MeasureAlmostBasic DerivationExceptionalSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_3_9]: COMPLETE Federer 3.3.9,
    pp. 295–296. For original arbitrary A of finite outer mass,
    original projection and original arbitrary B, infinite upper
    cone growth at each original B point and every positive radial
    cutoff implies zero Lebesgue outer mass of the ORIGINAL p(B).
    Every natural 0<=m<=n remains. Neither source is assumed measurable,
    bounded, purely unrectifiable or equal to the other. The proof
    derives finite local Radon regularisation and uses the actual
    infinite-upper-derivate null set of 2.9.5. *)
Theorem federer_3_3_9 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_measure phi ->(phi A< +oo)%E ->
  (forall x,B x ->structure_plane_infinite_growth m phi A x (structure_projection_kernel hmn p)) ->
  euclidean_lebesgue_measure m (euclidean_projection_linear p @` B)=0%E.
Proof.
move=>hStructure hFinite hGrowth.
have [psi [hReg [hPsi [hRadon [hTotal hValue]]]]]:=
  @structure_finite_projection_regularisation R n m phi A p hStructure hFinite.
have hNull:=@derivation_infinite_upper_points_null R
  (inner_metric_space (@euclidean_inner_productP R m))
  (@euclidean_lebesgue_measure R m) psi _ (euclidean_approximate_context R m) hPsi.
apply:(@measure_null_subset R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) _ _ _ hNull).
move=>z [x hx <-].
exact:(@structure_infinite_cone_projected_upper R n m hmn phi A p psi x
  hStructure.1 hPsi hValue (hGrowth x hx)).
Qed.
