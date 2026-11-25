(** Federer (1969), 4.1.14, p. 371: the
    compact-cutoff formula is independent of every
    admissible scalar cutoff. The difference has
    source support avoiding the target test's inverse
    image; the exact compact image support and the
    old support annihilation theorem give zero action. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces CurrentSupportGeometry CurrentContraction CurrentPointEvaluation
  CurrentSupportAgreement SmoothTestSpaces FlatCurrentsUP FlatCurrentUnion
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentLipschitzPushforwardUP CurrentLipschitzCutoffDifferenceSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzCutoffIndependence.
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
Hypothesis hT:@is_locally_flat_current R h2 n m U hU T.
Local Notation D0:=(@current_test_space R h2 n U hU 0%N).
Local Notation DT:=(@current_test_space R h2 nu V hV m).
Local Notation contract:=(fun gamma:D0=>@current_contraction R h2 n 0%N m U hU
  (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T).
Local Notation Push:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
  f hImage hLocal).
Local Notation action:=(@current_value R h2 nu V hV m).

(** Source for [current_lipschitz_cutoff_independent]:
    the two literal compact localizations give the
    same original target test value for every allowed
    gamma and delta, Federer 4.1.14, p. 371.
    No differentiability of f or extra global
    support/properness premise is used here. *)
Theorem current_lipschitz_cutoff_independent (phi:DT) (gamma delta:D0):
  @is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV T f phi gamma ->
  @is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV T f phi delta ->
  action (Push (contract gamma) (@hT gamma)) phi=
    action (Push (contract delta) (@hT delta)) phi.
Proof.
move=>hGamma hDelta.
pose S:=contract gamma-contract delta.
have hS:@is_flat_current R h2 n m U hU S.
  have h:=@flat_current_linear_combination R h2 n m U hU (-1)
    (contract delta) (contract gamma) (@hT delta) (@hT gamma).
  by rewrite scaleN1r addrC in h.
have hAvoidSource:=@current_lipschitz_cutoff_difference_support R h2 n nu m U V hU hV
  T f phi gamma delta hGamma hDelta.
have hAvoidTarget:forall y,@current_support R h2 nu V hV m (Push S hS) y ->
    ~@current_test_support R h2 nu m V hV phi y.
  move=>y hy.
  have[x hx <-]:=@current_flat_lipschitz_pushforward_support R h2 n nu m U V hU hV
    f hImage hLocal S hS y hy.
  exact:hAvoidSource x hx.
have hZero:=@current_test_disjoint_support_zero R h2 nu m V hV (Push S hS) phi hAvoidTarget.
have hDifference:=@current_flat_lipschitz_pushforward_subtract R h2 n nu m U V hU hV
  f hImage hLocal (contract gamma) (contract delta) (@hT gamma) (@hT delta) hS.
rewrite hDifference in hZero.
pose E:=@current_point_evaluation R h2 nu m V hV phi.
change (E (Push (contract gamma) (@hT gamma)-Push (contract delta) (@hT delta))=0)
  in hZero.
rewrite (linB (hom_linear E)) in hZero.
apply/eqP;rewrite -subr_eq0;exact/eqP.
Qed.
End CurrentLipschitzCutoffIndependence.
