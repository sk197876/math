(** Federer (1969), 4.1.14, p. 371: the
    local cutoff equation also holds for each
    original compact flat image. Choose the
    already proved local image; compact agreement
    identifies it with the global compact image.
    No nonsmooth composition is used as a
    scalar test. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP OpenLocalLipschitzCompact SmoothCompactSet CurrentSpaces
  CurrentContraction SmoothTestSpaces FlatCurrentsUP FlatCurrentScalarClosure
  CurrentLipschitzCompactImage CurrentCompactMapProper CurrentProperSupport
  CurrentLipschitzPushforwardUP CurrentLipschitzPushforwardSealed
  CurrentLipschitzImageCompactAgreement CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFlatLipschitzCutoffAction.
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
Hypothesis hT:@is_flat_current R h2 n m U hU T.
Local Notation contract gamma:=(@current_contraction R h2 n 0%N m U hU
  (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T).
Local Notation Push:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hImage hLocal).

(** Source for [current_flat_lipschitz_pushforward_cutoff_action]:
    the original compact image evaluates every
    allowed local cutoff, Federer 4.1.14, p. 371.
    The exact interior plateau remains required;
    no properness, normality or finite mass is
    an extra premise for this compact input. *)
Theorem current_flat_lipschitz_pushforward_cutoff_action
    (phi:@current_test_space R h2 nu V hV m)
    (gamma:@current_test_space R h2 n U hU 0%N)
    (hGamma:@is_flat_current R h2 n m U hU (contract gamma)):
  @is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV
    T f phi gamma ->
  @current_value R h2 nu V hV m (Push T hT) phi=
    @current_value R h2 nu V hV m (Push (contract gamma) hGamma) phi.
Proof.
move=>hCutoff.
have[K hKT]:=hT.
pose hCompact:=@flat_supported_current_compact R h2 n m U hU K T hKT.
pose hf:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hLocal.
pose hProper:=@current_compact_map_proper R h2 n nu m U V hU T f hImage hf hCompact.
have hLocalT:@is_locally_flat_current R h2 n m U hU T.
  move=>delta;exact:(@flat_current_scalar_multiplier R h2 n m U hU delta T hT).
pose Q:=@CurrentLipschitzPushforward.value R h2 n nu m U V hU hV
  f hImage hLocal T hLocalT hProper.
pose hQ:=@CurrentLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hImage hLocal T hLocalT hProper.
have hAgreement:=@current_lipschitz_image_compact_agreement R h2 n nu m
  U V hU hV f hImage hLocal T hT Q hQ.
have hAction:@current_value R h2 nu V hV m Q phi=
    @current_value R h2 nu V hV m (Push (contract gamma) hGamma) phi.
  exact:(hQ.2 phi gamma hGamma hCutoff).
have hValueAgreement:=congr1
  (fun P=>@current_value R h2 nu V hV m P phi) hAgreement.
exact:(eq_trans (esym hValueAgreement) hAction).
Qed.
End CurrentFlatLipschitzCutoffAction.
