(** Federer (1969), 4.1.14, p. 371: the
    original all-set variation inequality for the actual
    opaque flat-current image. Choose a compact index
    only inside the proof. The original finite mass
    and continuous Lebesgue-AE differential majorant suffice;
    both integration representations are conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentDomain CurrentSpaces CurrentMassSealed CurrentIntegrationCriterion
  CurrentFiniteMassRepresentation NormalisedCurrentSealed CurrentProperSupportDomain
  FlatCurrentsUP CurrentFlatLipschitzPushforwardSealed
  CurrentCompactMajorantApproximationUP CurrentFiniteMassLipschitzMajorantVariation
  MeasureDensity MeasurePushforward SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatLipschitzMajorantVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Hypothesis hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E.
Variable sigma:X->R^o.
Hypothesis hSigma:norm_class_zero NX (fun t:R^o=>`|t|) U sigma.
Hypothesis hMajorant:@is_current_ae_differential_majorant R n nu U f sigma.
Local Notation Q:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hImage hLocal T hFlat).

(** Source for [current_flat_lipschitz_majorant_variation]: the
    literal ||f#T|| <= f#(||T|| sigma^m) on
    every set in Federer 4.1.14, p. 371,
    for the actual original F_m(U) operator.
    No compact index, candidate image, normality or
    variation-AE derivative hypothesis is an extra premise.
    Every original source and image representation is allowed. *)
Theorem current_flat_lipschitz_majorant_variation:
  @is_integration_representable_current R h2 n m U hU T /\
  @is_integration_representable_current R h2 nu m V hV Q /\
  forall hSource:@is_integration_representable_current R h2 n m U hU T,
    forall hTarget:@is_integration_representable_current R h2 nu m V hV Q,
      forall B,(@NormalisedCurrent.measure R h2 nu m V hV Q hTarget B<=
        measure_pushforward (@current_map_on_domain R n nu U V f hImage)
          (measure_with_density (@NormalisedCurrent.measure R h2 n m U hU T hSource)
            (real_total_integrand (fun x:current_domain R n U=>
              ((sigma (set_val x))^+m)%R))) B)%E.
Proof.
have hSource:=@current_finite_mass_representation R h2 n m U hU T hFinite.
have[K hK]:=hFlat.
have hPoint:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m
  U V hU hV f hImage hLocal T hFlat).2 K hK.
have[hTarget hBound]:=@current_finite_mass_lipschitz_image_majorant_variation
  R h2 n nu m U V hU hV f hImage hLocal K T Q sigma
  hK hFinite hPoint hSigma hMajorant.
split;first exact:hSource.
split;first exact:hTarget.
exact:hBound.
Qed.
End CurrentFlatLipschitzMajorantVariation.

Arguments current_flat_lipschitz_majorant_variation : clear implicits.
