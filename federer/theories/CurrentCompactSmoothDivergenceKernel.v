(** Federer (1969), 4.1.18, p. 377: every
    original compact smooth graph pair is in
    ker q. Zero extension retains both
    smooth fields, and the old whole-space
    boundary identity restricts back to U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms CurrentSpaces
  CurrentVectorSpaces SmoothFunctionSpaceUP CurrentBoundary
  CurrentOpenRestriction CurrentOpenRestrictionBoundary CurrentIntegrationCriterion
  CurrentSmoothLebesgue CurrentSmoothLebesgueFullRepresentation
  CurrentOpenDensityActionUnique CurrentSmoothDivergenceKernel
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CompactSummableCurrentZeroExtension
  EuclideanOpenDomainMeasure EuclideanFullDomainMeasure
  CurrentLonePairImageUP CurrentLonePairImageSealed
  SmoothCurrentDivergence CurrentCompactSmoothDivergenceUP
  CurrentCompactSmoothDivergenceSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothDensityRestriction.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n d : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation FT := (current_domain R n Full).
Local Notation E := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation F := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation O := (@compact_summable_multivector_space R h2 n d U hU).
Local Notation value := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 n d U hU).
Local Notation image := (@compact_summable_multivector_current R h2 n d U hU).
Local Notation inclusion := (fun (x : X) (_ : U x) => Logic.I).
Local Notation restriction :=
  (@current_open_restriction R h2 n d U Full hU hFull inclusion).

(** Source for [current_compact_smooth_density_restriction]:
    the original smooth Omega density current
    is the restriction of its actual whole-space
    smooth density current, supporting the graph
    argument in Federer 4.1.18, p. 377.
    This adapter composes the preceding zero-extension
    current law with the old smooth representation. *)
Theorem current_compact_smooth_density_restriction
    (eta : E) (zeta : F) (xi : O) :
  fv zeta=ev eta -> value xi=(fun x : UT => ev eta (set_val x)) ->
  image xi=restriction (@current_smooth_lebesgue_map R h2 n d zeta).
Proof.
move=> hSmooth hValue.
have hRaw : raw xi=fv zeta.
  apply: funext=> x; case: (pselect (U x))=> hx.
  - pose y : UT := exist _ x (mem_set hx).
    change (raw xi (set_val y)=fv zeta (set_val y)).
    by rewrite compact_summable_multivector_ambient_inside hValue hSmooth.
  - rewrite (@compact_summable_multivector_ambient_outside R h2 n d U hU xi x hx)
      hSmooth.
    exact: esym (smooth_function_evaluation_outside hE eta hx).
have [theta [hTheta hSize]] :=
  @compact_summable_multivector_ambient_representative R h2 n d U hU xi.
have hCurrent := @compact_summable_current_zero_extension R h2 n d U hU
  xi theta hTheta.
have hRepresentation := @compact_summable_multivector_current_representation R h2 n d
  Full hFull theta.
rewrite hTheta hRaw in hRepresentation.
have hEqual : @compact_summable_multivector_current R h2 n d Full hFull theta=
    @current_smooth_lebesgue_map R h2 n d zeta.
  exact: (@current_open_density_action_unique R h2 n d Full hFull
    (@euclidean_open_domain_measure R n Full)
    (fun x : FT => fv zeta (set_val x))
    (@compact_summable_multivector_current R h2 n d Full hFull theta)
    (@current_smooth_lebesgue_map R h2 n d zeta) hRepresentation
    (@current_smooth_lebesgue_full_representation R h2 n d zeta)).
by rewrite hEqual in hCurrent.
Qed.
End SmoothDensityRestriction.

Section GraphKernel.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation fv d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation divF := (@smooth_current_divergence R h2 n m Full hFull).
Local Notation L d := (@current_smooth_lebesgue_map R h2 n d).
Local Notation inclusion := (fun (x : X) (_ : U x) => Logic.I).
Local Notation restriction d :=
  (@current_open_restriction R h2 n d U Full hU hFull inclusion).

(** Source for [current_compact_smooth_divergence_pair_kernel]:
    the original smooth graph set lies in
    ker q, Federer 4.1.18, p. 377.
    The sign is positive in (div eta,eta)
    because the actual density boundary is
    minus the divergence density. No normality
    or separate mass premise is introduced. *)
Theorem current_compact_smooth_divergence_pair_kernel (v : P) :
  @is_current_compact_smooth_divergence_pair R h2 n m U hU v ->
  @CurrentLonePair.map R h2 n m U hU v=0.
Proof.
move=> [eta [K [hSupport [hLeft hRight]]]].
have [zeta [hValue hDiv]] :=
  @current_compact_smooth_divergence_zero_extension R h2 n m U hU K eta hSupport.
have hFirst := @current_compact_smooth_density_restriction R h2 n m U hU
  (div eta) (divF zeta) v.1 hDiv hLeft.
have hSecond := @current_compact_smooth_density_restriction R h2 n m.+1 U hU
  eta zeta v.2 hValue hRight.
rewrite (@CurrentLonePair.laws R h2 n m U hU v) hFirst hSecond.
rewrite -(@current_open_restriction_boundary R h2 n m U Full hU hFull
  inclusion (L m.+1 zeta)).
rewrite -(linD (hom_linear (restriction m))).
by rewrite (@current_smooth_divergence_pair_kernel R h2 n m zeta) linear0.
Qed.
End GraphKernel.
