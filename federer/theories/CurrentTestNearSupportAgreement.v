(** Federer (1969), 4.1.7, p. 359:
    changing a test away from spt T
    does not change its current value.
    This supporting consequence of the original
    support definition proves independence of the
    compact cutoff in the pushforward. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentSupportGeometry CurrentSupportAgreement SmoothTestSpaces SmoothTestEvaluation
  SmoothLocalAgreementSeminorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTestNearSupportAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Variable T:@current_space R h2 n U hU m.

(** Source for [current_test_near_support_values_equal]:
    tests agreeing on an open
    neighbourhood of the whole original
    current support have equal current
    values, supporting Federer 4.1.7,
    p. 359. Pointwise agreement on
    the support alone is not substituted
    for the required neighbourhood agreement. *)
Theorem current_test_near_support_values_equal (psi chi:DT) (W:set X):
  @open (real_norm_metric_space hNX) W->
  @current_support R h2 n U hU m T `<=` W->
  (forall x,W x->value psi x=value chi x)->
  @current_value R h2 n U hU m T psi=@current_value R h2 n U hU m T chi.
Proof.
move=>hW hSupport hAgreement.
have hZero x (hx:W x):value (psi-chi) x=0.
  have hDifference:value (psi-chi) x=value psi x-value chi x.
    change (smooth_test_values_hom hE (psi-chi) x=
      smooth_test_values_hom hE psi x-smooth_test_values_hom hE chi x).
    by rewrite linearB.
  by rewrite hDifference (hAgreement x hx) subrr.
have hDisjoint x (hx:@current_support R h2 n U hU m T x):
    ~@current_test_support R h2 n m U hU (psi-chi) x.
  exact:(@smooth_support_avoids_open_zero_set R X Y NX hNX U DT value
    (psi-chi) W hW hZero x (hSupport x hx)).
have hAction:=@current_test_disjoint_support_zero R h2 n m U hU T (psi-chi) hDisjoint.
rewrite linearB in hAction;apply/eqP;rewrite -subr_eq0;exact/eqP.
Qed.
End CurrentTestNearSupportAgreement.
