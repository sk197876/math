(** Federer (1969), 4.1.9, p. 363: the point current
    evaluates original smooth forms by the same literal point
    pairing. Reuse the unique smooth-dual extension of the
    actual compactly supported current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentCoefficientNorms SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothCutoffReplacement CurrentCompactSmoothValue CurrentCompactSmoothAgreement
  PointMultivectorCurrentSealed PointMultivectorCurrentSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section PointMultivectorCurrentSmooth.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Local Notation Form := (A_m X R^o j).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NF := (@current_form_comass R h2 n j).
Local Notation hNF := (@current_form_comass_real_norm R h2 n j).
Variable U:set X.
Hypothesis hU:forall y,U y->norm_domain_interior NX U y.
Variable x:X.
Hypothesis hx:U x.
Local Notation K := (@smooth_compact_singleton R X NX hNX U x hx).
Local Notation P := (@PointMultivectorCurrent.value R h2 n j U hU x hx).
Local Notation hCompact := (fun eta:exterior_power X j=>@point_multivector_current_compact R h2 n j U hU x hx eta).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU j).

(** Source for [point_multivector_current_smooth_value]: the
    original point action remains <eta,phi(x)> for every
    actual smooth phi, supporting the differential-form
    homotopy identities in Federer 4.1.9, p. 363.
    The proof also covers the zero current. *)
Theorem point_multivector_current_smooth_value eta (phi:E):
  @current_compact_smooth_value R h2 n j U hU (P eta) (hCompact eta) phi=
    pairing eta (ev phi x).
Proof.
pose Q:=@smooth_cutoff_replacement R X Form NX NF hNX hNF n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE K.
have[W [hW [hKW [hWU hAgreement]]]]:=
  @smooth_cutoff_replacement_agrees_near_compact R X Form NX NF hNX hNF n
    (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE K.
have hSupport:forall y,@current_support R h2 n U hU j (P eta) y->W y.
  move=>y hy;apply:hKW;exact:(@point_multivector_current_support R h2 n j U hU x hx eta y hy).
have hValue:=@current_compact_near_support_smooth_value R h2 n j U hU (P eta) (hCompact eta)
  phi (Q phi) W hW hSupport (fun y hy=>esym (@hAgreement phi y hy)).
rewrite hValue (@PointMultivectorCurrent.laws R h2 n j U hU x hx eta (Q phi)).
change (pairing eta (ev (smooth_test_inclusion hE (Q phi)) x)=pairing eta (ev phi x)).
by rewrite (@hAgreement phi x (hKW x (erefl x))).
Qed.
End PointMultivectorCurrentSmooth.
