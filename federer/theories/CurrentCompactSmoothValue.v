(** Federer (1969), 4.1.8, p. 361: evaluation
    of a compactly supported current on original smooth
    forms uses its unique smooth-dual extension. The public
    restriction and support laws are inherited from 4.1.7,
    p. 355, and 4.1.1, pp. 344–345. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms AlternatingZero
  CurrentSpaces CurrentCoefficientNorms CurrentConstantFields CurrentCompactExtensionUP CurrentCompactExtensionSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology
  SmoothDualRestriction SmoothDualCompactImage ContinuousRealDual FunctionalSupportUP NormOpenTopology OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactSmoothValue.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation EO := (smooth_function_opens hD).
Local Notation hEO := (smooth_function_topology_laws hD).1.
Local Notation CD := (@current_space R h2 n U hU m).
Local Notation rho := (@current_smooth_dual_restriction R h2 n U hU m).
Variable T:CD.
Hypothesis hCompact:@compact (real_norm_metric_space hNX) [set x|@current_support R h2 n U hU m T x].
Local Notation L := (@CompactCurrentExtension.value R h2 n m U hU T hCompact).
Local Notation eE := (@continuous_real_dual_evaluation R E EO hEO).

(** Source for [current_compact_smooth_value]: the original
    smooth-form action of a compactly supported current,
    supporting S(1) in Federer 4.1.8, p. 361.
    The independently specified unique extension stays opaque. *)
Definition current_compact_smooth_value:Hom E R^o:=eE L.

(** Source for [current_compact_smooth_value_continuous]: this
    original extension is continuous on the actual smooth
    space, supporting Federer 4.1.8, p. 361,
    by the compact-support image of 4.1.7, p. 355. *)
Theorem current_compact_smooth_value_continuous:
  open_family_continuous EO (norm_open_family (@scalar_absolute_value_norm R)) current_compact_smooth_value.
Proof. exact:(@continuous_real_dual_member_continuous R E EO hEO L). Qed.

(** Source for [current_compact_smooth_test_value]: the original
    extension agrees with the given current on every actual
    compact test, supporting Federer 4.1.8, p. 361. *)
Theorem current_compact_smooth_test_value (psi:@current_test_space R h2 n U hU m):
  current_compact_smooth_value (smooth_test_inclusion hE psi)=
    @current_value R h2 n U hU m T psi.
Proof.
have hRestriction:rho L=T:=@CompactCurrentExtension.laws R h2 n m U hU T hCompact.
have hValue:@current_value R h2 n U hU m (rho L) psi=eE L (smooth_test_inclusion hE psi).
  exact:(@smooth_dual_test_restriction_evaluation R X Y NX NY hNX hNY U E ev hE D hD L psi).
exact:(eq_trans (esym hValue) (congr1 (fun S:CD=>@current_value R h2 n U hU m S psi) hRestriction)).
Qed.

(** Source for [current_compact_smooth_support]: the smooth
    extension has exactly the original current support,
    supporting Federer 4.1.8, p. 361, by the
    already proved support-preserving restriction of 4.1.1. *)
Theorem current_compact_smooth_support:
  @smooth_functional_support R X Y NX hNX U E ev current_compact_smooth_value=
    @current_support R h2 n U hU m T.
Proof.
have hRestriction:rho L=T:=@CompactCurrentExtension.laws R h2 n m U hU T hCompact.
have hSupport:@current_support R h2 n U hU m (rho L)=
    @smooth_functional_support R X Y NX hNX U E ev (eE L).
  exact:(@smooth_dual_restriction_support R X Y NX NY hNX hNY n
    (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE D hD L).
rewrite hRestriction in hSupport;exact:esym hSupport.
Qed.

(** Source for [current_compact_smooth_value_independent]: the
    action does not depend on a compactness proof,
    supporting the original unambiguous S(1) in Federer
    4.1.8, p. 361. Uniqueness follows from the
    public original restriction law. *)
Theorem current_compact_smooth_value_independent
    (hOther:@compact (real_norm_metric_space hNX) [set x|@current_support R h2 n U hU m T x]):
  eE L=eE (@CompactCurrentExtension.value R h2 n m U hU T hOther).
Proof.
have hEqual:L=@CompactCurrentExtension.value R h2 n m U hU T hOther.
  apply:(@current_compact_extension_unique R h2 n m U hU T).
  - exact:(@CompactCurrentExtension.laws R h2 n m U hU T hCompact).
  - exact:(@CompactCurrentExtension.laws R h2 n m U hU T hOther).
by rewrite hEqual.
Qed.
End CurrentCompactSmoothValue.

(** Source for [current_compact_total]: the literal original
    S(1) in the zero-dimensional-current projection formula,
    Federer 4.1.8, p. 361. The constant one is
    an actual smooth zero-form and need not be a test. *)
Definition current_compact_total (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU 0%N)
    (hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      [set x|@current_support R h2 n U hU 0%N T x]):R^o:=
  @current_compact_smooth_value R h2 n 0%N U hU T hCompact
    (@current_constant_form R h2 n U hU 0%N (@zero_form R (R_n R n) R^o 1)).
