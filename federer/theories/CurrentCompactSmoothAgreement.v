(** Federer (1969), 4.1.8, p. 361: the value S(1)
    equals the value on any compact scalar test equal
    to one near the whole original support. Prove the
    general smooth/test agreement from the already proved
    support law of the original smooth-dual extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms AlternatingZero
  CurrentSpaces CurrentCoefficientNorms CurrentConstantFields CurrentCompactSmoothValue
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothLocalAgreementSeminorm
  SmoothDualFunctionalSupport FunctionalSupportUP NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactSmoothAgreement.
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
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation inc := (smooth_test_inclusion hE).
Variable T:@current_space R h2 n U hU m.
Hypothesis hCompact:@compact (real_norm_metric_space hNX) [set x|@current_support R h2 n U hU m T x].
Local Notation L := (@current_compact_smooth_value R h2 n m U hU T hCompact).

(** Source for [current_compact_near_support_smooth_value]:
    a smooth form and an actual compact test agreeing
    near the whole original current support have the
    same extended current value, supporting S(1) in
    Federer 4.1.8, p. 361, by 4.1.1,
    pp. 344–345. Pointwise support agreement is not substituted. *)
Theorem current_compact_near_support_smooth_value (phi:E) (psi:DT) (W:set X):
  @open (real_norm_metric_space hNX) W->
  (@current_support R h2 n U hU m T `<=` W)->
  (forall x,W x->ev phi x=@current_test_value R h2 n U hU m psi x)->
  L phi=@current_value R h2 n U hU m T psi.
Proof.
move=>hW hSW hPoint.
have hZero x (hx:W x):ev (phi-inc psi) x=0.
  have hDifference:ev (phi-inc psi) x=ev phi x-@current_test_value R h2 n U hU m psi x.
    exact:(congr1 (fun f:X->Y=>f x) (linearB (smooth_function_values_hom hE) phi (inc psi))).
  by rewrite hDifference (@hPoint x hx) subrr.
have hDisjoint x (hx:@smooth_functional_support R X Y NX hNX U E ev L x):
    ~@smooth_function_support R X Y NX hNX U E ev (phi-inc psi) x.
  have hT:@current_support R h2 n U hU m T x.
    rewrite -(@current_compact_smooth_support R h2 n m U hU T hCompact);exact:hx.
  exact:(@smooth_support_avoids_open_zero_set R X Y NX hNX U E ev
    (phi-inc psi) W hW hZero x (hSW x hT)).
have hDifferenceZero:=@smooth_dual_disjoint_support_zero R X Y NX NY hNX hNY n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE D hD L (phi-inc psi)
  (@current_compact_smooth_value_continuous R h2 n m U hU T hCompact) hDisjoint.
rewrite (linB (hom_linear L)) in hDifferenceZero.
have hEqual:L phi=L (inc psi).
  apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hDifferenceZero.
exact:(eq_trans hEqual (@current_compact_smooth_test_value R h2 n m U hU T hCompact psi)).
Qed.
End CurrentCompactSmoothAgreement.

(** Source for [current_compact_total_cutoff]: every genuine
    compact scalar test equal to one on an open
    neighbourhood of spt S has value S(1), supporting
    the original projection formula of Federer 4.1.8,
    p. 361. The constant one is evaluated in E. *)
Theorem current_compact_total_cutoff (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU 0%N)
    (hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      [set x|@current_support R h2 n U hU 0%N T x])
    (gamma:@current_test_space R h2 n U hU 0%N) (W:set (R_n R n)):
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W->
  (@current_support R h2 n U hU 0%N T `<=` W)->W `<=` U->
  (forall x,W x->@current_test_value R h2 n U hU 0%N gamma x=@zero_form R (R_n R n) R^o 1)->
  @current_value R h2 n U hU 0%N T gamma=@current_compact_total R h2 n U hU T hCompact.
Proof.
move=>hW hSW hWU hOne;symmetry.
apply:(@current_compact_near_support_smooth_value R h2 n 0%N U hU T hCompact
  (@current_constant_form R h2 n U hU 0%N (@zero_form R (R_n R n) R^o 1)) gamma W hW hSW).
move=>x hx.
rewrite (@current_constant_form_values R h2 n U hU 0%N (@zero_form R (R_n R n) R^o 1)
  x (@hWU x hx)).
symmetry;exact:(@hOne x hx).
Qed.
