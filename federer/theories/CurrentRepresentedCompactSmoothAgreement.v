(** Federer (1969), 4.1.7–4.1.8, pp. 357–361,
    used in 4.1.12, p. 368: the original
    smooth extension of a compact represented current
    depends only on form values on its support.
    Reduce to actual tests by the existing cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentIntegrationCriterion CurrentCompactSmoothValue CurrentCompactSmoothAgreement
  CurrentRepresentedSupportAgreement SmoothCompactSet SmoothCutoffReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentRepresentedCompactSmoothAgreement.
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
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hCompact:@compact (real_norm_metric_space hNX) (@current_support R h2 n U hU m T).
Local Notation L := (@current_compact_smooth_value R h2 n m U hU T hCompact).

(** Source for [current_represented_compact_smooth_values_equal]:
    two smooth forms with equal values on the
    support have equal extended values on a compact
    represented current, by Federer 4.1.7–4.1.8,
    pp. 357–361. This supports 4.1.12, p. 368;
    representation is retained as a hypothesis. *)
Theorem current_represented_compact_smooth_values_equal (phi psi:E):
  (forall x,@current_support R h2 n U hU m T x->ev phi x=ev psi x)->L phi=L psi.
Proof.
move=>hEqual.
pose K:=@Build_smooth_compact_set R X NX hNX U
  (@current_support R h2 n U hU m T) (fun x hx=>hx.1) hCompact.
pose Q:=@smooth_cutoff_replacement R X Y NX NY hNX hNY n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE K.
have[W [hW [hKW [hWU hAgree]]]]:=
  @smooth_cutoff_replacement_agrees_near_compact R X Y NX NY hNX hNY n
    (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE K.
have hCut f:L f=@current_value R h2 n U hU m T (Q f).
  apply:(@current_compact_near_support_smooth_value R h2 n m U hU T hCompact f (Q f) W hW hKW).
  move=>x hx;symmetry;exact:(hAgree f x hx).
rewrite !hCut.
apply:(@current_represented_support_values_equal R h2 n m U hU T hT)=>x hx.
change (ev (SmoothTestSpaces.smooth_test_inclusion hE (Q phi)) x=
  ev (SmoothTestSpaces.smooth_test_inclusion hE (Q psi)) x).
rewrite (hAgree phi x (hKW x hx)) (hAgree psi x (hKW x hx));exact:hEqual x hx.
Qed.
End CurrentRepresentedCompactSmoothAgreement.
