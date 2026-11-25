(** Federer (1969), 4.1.8, p. 360: the current slice
    is smooth in its remaining variables. This supporting
    whole-space theorem reuses the original test quotient of
    4.1.1, p. 346, and the coordinate class criterion
    already used for regularisation in 4.1.2, p. 347. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormPartialDerivative NormRegularity GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  SmoothGlobalTranslationSealed TestGlobalTranslation DistributionDirectionalDerivative
  DistributionTranslationContinuity DistributionTranslationDirectional
  CoordinateClassSuccessor ContinuousRealDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section DistributionTranslationSmoothness.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior NX x).
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation L := (@SmoothGlobalTranslation.operator R X Y NX NY hNX hNY E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R X Y NX NY hNX hNY E ev hE).
Local Notation A := (fun c=>@test_global_translation R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).
Local Notation Q := (fun v=>@distribution_test_directional_derivative R X Y NX NY hNX hNY
  (fun _=>True) hFull E ev hE D hD v).

(** Source for [distribution_translation_orbit_class]: every
    finite smoothness class of the translated-test pairing,
    supporting Federer 4.1.8, p. 360. The induction applies
    the preceding coordinate derivative laws to actual tests. *)
Theorem distribution_translation_orbit_class (T:DD) k:
  forall f:DT,norm_class hNX hNS (fun _=>True) (fun c=>eD T (A c f)) k.
Proof.
have hContinuous f:=@distribution_translation_orbit_continuous R X Y NX NY hNX hNY
  n (@coordinate_basis R n) (@coordinate_basisP R n) E ev hE D hD T f.
elim:k=>[|k IH] f.
- exact:(@norm_class_zeroP R X R^o NX (fun t:R^o=>`|t|) hNX hNS
    (fun _=>True) (fun c=>eD T (A c f))).2 (hContinuous f).
- pose p:=fun i:'I_n=>fun c=>eD T (A c (Q (@coordinate_basis R n i) f)).
  apply:(@norm_class_successor_coordinate_fields R n R^o (fun t:R^o=>`|t|) hNS
    (fun c=>eD T (A c f)) p k (hContinuous f)).
  + move=>c i.
    exact:(@distribution_translation_orbit_directional R X Y NX NY hNX hNY
      n (@coordinate_basis R n) (@coordinate_basisP R n) E ev hE D hD T f c
      (@coordinate_basis R n i)).
  + move=>i; exact:IH.
Qed.

(** Source for [distribution_translation_orbit_smooth]: an
    arbitrary distribution evaluated on translates of an actual
    test gives a smooth scalar function, supporting the
    smooth-slice construction in Federer 4.1.8, p. 360.
    The statement includes the zero-dimensional source. *)
Theorem distribution_translation_orbit_smooth (T:DD) (f:DT):
  norm_class_all_orders hNX hNS (fun _=>True) (fun c=>eD T (A c f)).
Proof. move=>k; exact:distribution_translation_orbit_class. Qed.
End DistributionTranslationSmoothness.
