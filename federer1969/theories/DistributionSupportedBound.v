(** Federer (1969), 4.1.2, p. 347: the
    original finite-order continuity bound applies to every
    actual test supported in the chosen compact set.
    This is the same-K criterion of 4.1.1, p. 345. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenTopology OpenFamilyTopologyUP
  ContinuousMultilinearSealed LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology
  DistributionLocalBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_supported_local_bound]: finite-order
    distribution bounds used in the smoothing argument of
    Federer 4.1.2, p. 347, retain the
    original supporting compact and integer order and constant. *)
Theorem distribution_supported_local_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (hU:forall x,U x ->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY U ev)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    (T:Hom (smooth_test_space hE) R^o):
  open_family_continuous (smooth_test_opens hE hD)
    (norm_open_family (@scalar_absolute_value_norm R)) T ->
  forall K:smooth_compact_set hNX U,exists i M:nat,forall f:smooth_test_space hE,
    @smooth_function_support R X Y NX hNX U E ev (smooth_test_inclusion hE f) `<=`
      smooth_compact_carrier K ->
    `|T f|<=M%:R * smooth_function_derivative_seminorm hD K i (smooth_test_inclusion hE f).
Proof.
move=>hT K.
have[i [M hBound]]:=(@distribution_continuity_local_bound R X Y NX NY hNX hNY U hU E ev hE D hD T).1 hT K.
exists i,M=>f hSupport.
have[g hg]:=subspace_representation_full (smooth_fixed_test_space_laws hE K) hSupport.
have hSame:smooth_test_step hE K g=f.
  apply:(subspace_representation_injective (smooth_test_space_laws hE)).
  by rewrite smooth_test_step_evaluation hg.
have h:=hBound g; by rewrite hSame hg in h.
Qed.
