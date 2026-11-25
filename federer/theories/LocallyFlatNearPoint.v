(** Federer (1969), 4.1.12, p. 368: a
    locally flat current agrees with a flat current
    near every point. Reuse the original compact
    scalar cutoffs and the preceding plateau and
    support-agreement theorems of 4.1.7. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet SmoothTestSpaces
  CurrentContraction CurrentSupportGeometry CurrentSupportAgreement CurrentScalarCutoffs CurrentScalarPlateau
  FlatCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocallyFlatNearPoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation hE0 := (@current_smooth_space_laws R h2 n U hU 0%N).

(** Source for [locally_flat_near_point_flat]: every
    x in U admits S in F_m(U) with x outside
    spt(T-S), the forward implication of the
    original local criterion in Federer 4.1.12,
    p. 368. No countable exhaustion is introduced. *)
Theorem locally_flat_near_point_flat (T:C):
  @is_locally_flat_current R h2 n m U hU T->
    @is_germwise_flat_current R h2 n m U hU T.
Proof.
move=>hT x hx.
pose K:=@smooth_compact_singleton R X NX hNX U x hx.
have [gamma [W [hW [hKW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n U hU K.
pose a:=smooth_test_inclusion hE0 gamma.
pose S:=@current_contraction R h2 n 0%N m U hU a T.
exists S;split;first exact:hT gamma.
have hAgreement:forall psi:@current_test_space R h2 n U hU m,
    @current_test_support R h2 n m U hU psi `<=` W->
    @current_value R h2 n U hU m T psi=@current_value R h2 n U hU m S psi.
  move=>psi hPsi;rewrite current_contraction_evaluation.
  by rewrite (@current_scalar_test_local_plateau R h2 n m U hU W a hOne psi hPsi).
have hBound:=@current_support_difference_agreement R h2 n m U hU T S W hW hAgreement.
move=>hSupport;exact:(hBound x hSupport).2 (hKW x (erefl x)).
Qed.
End LocallyFlatNearPoint.
