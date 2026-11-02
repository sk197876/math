(** Federer (1969), 3.1.13, pp. 224–225:
    a countable smooth partition for an arbitrary
    family of open subsets of R^m, with the
    printed geometric selection and quantitative derivative bounds.
    All construction witnesses are used through their laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness ContinuousMultilinearUP NormHigherDifferentialUP
  InnerSmoothUnitBump InnerBumpDerivativeSuprema UniformFunctionNormUP
  FedererCoverRadius EuclideanPartitionBallCoverUP EuclideanPartitionBallCover
  EuclideanPartitionFamilyUP EuclideanPartitionFamilySealed EuclideanPartitionFamilyLaws
  EuclideanPartitionDenominatorBounds EuclideanPartitionNormalizedBounds
  PartitionDerivativeBoundsUP PartitionDerivativeBoundsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PartitionExistence.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N
  (fun t : R^o=>`|t|) (@ev i) (@ZN i).

(** Source for [federer_smooth_partition_exists]:
    the smooth partition construction and both
    displayed higher-derivative bounds in Federer
    3.1.13, pp. 224–225.
    G_i is exactly sup im ||D^i mu||;
    G and V are chosen before the open
    family Phi. Empty covers and dimension
    zero are retained. The family specification
    includes global smoothness and compact support,
    and its public laws give the refinement
    and the vanishing positive-order derivative sums. *)
Theorem federer_smooth_partition_exists :
  exists (Dmu : forall i, X->Z i) (G V : nat->R),
    (forall i x, has_norm_higher_differential N ev ZN
      (fun _=>True) (inner_smooth_unit_bump (@euclidean_inner_productP R m)) i x (Dmu i x)) /\
    (forall i, is_uniform_function_norm (fun x=>@ZN i (Dmu i x)) (G i)) /\
    is_partition_derivative_bounds ((129 : R)^+m) G V /\
    forall Phi : set (set X), (forall T, Phi T -> open T) ->
      exists (S : set X) (sigma : X->R) (v : X->X->R),
        is_federer_partition_ball_cover Phi S /\
        is_euclidean_partition_family ev ZN Phi S sigma v /\
        (forall i x (z : Z i), (\bigcup_(T in Phi) T) x ->
          has_norm_higher_differential N ev ZN (\bigcup_(T in Phi) T) sigma i x z ->
          @ZN i z<=129^+m*G i/(federer_cover_radius Phi x)^+i) /\
        forall s, S s -> forall i x (z : Z i), (\bigcup_(T in Phi) T) x ->
          has_norm_higher_differential N ev ZN (\bigcup_(T in Phi) T) (v s) i x z ->
          @ZN i z<=V i/(federer_cover_radius Phi x)^+i.
Proof.
have hex i : exists p : (X->Z i)*R,
    (forall x, has_norm_higher_differential N ev ZN
      (fun _=>True) (inner_smooth_unit_bump (@euclidean_inner_productP R m)) i x (p.1 x)) /\
    is_uniform_function_norm (fun x=>@ZN i (p.1 x)) p.2.
  have [D [G [hD [hG _]]]] := inner_bump_derivative_supremum_exists
    (@coordinate_basisP R m) hZ i.
  by exists (D,G).
pose p i := projT1 (cid (hex i)).
pose Dmu i := (p i).1.
pose G i := (p i).2.
have hDmu i := (projT2 (cid (hex i))).1.
have hG i := (projT2 (cid (hex i))).2.
pose V := @PartitionDerivativeBounds.value R (129^+m) G.
have hV : is_partition_derivative_bounds ((129 : R)^+m) G V :=
  PartitionDerivativeBounds.laws _ _.
exists Dmu, G, V; split; first exact hDmu.
split; first exact hG; split; first exact hV.
move=>Phi ho.
have [S hS] := federer_partition_ball_cover_exists ho.
pose sigma := @EuclideanPartitionFamily.denominator R m Z ev ZN hZ Phi S ho hS.
pose v := @EuclideanPartitionFamily.functions R m Z ev ZN hZ Phi S ho hS.
have hfamily := @EuclideanPartitionFamily.laws R m Z ev ZN hZ Phi S ho hS.
exists S, sigma, v; split; first exact hS; split; first exact hfamily.
split.
- move=>i x z hx hz.
  exact: (@euclidean_partition_denominator_derivative_bound R m Z ev ZN hZ
    Phi S ho hS sigma v hfamily i (Dmu i) (G i) (hDmu i) (hG i) x z hx hz).
- exact: (@euclidean_partition_normalized_derivative_bound R m Z ev ZN hZ
    Dmu G V hDmu hG hV Phi S ho hS sigma v hfamily).
Qed.
End PartitionExistence.
