(** Federer (1969), 4.1.9, p. 363: existence of the
    linear homotopy operator on actual smooth forms. A common
    local Cartesian slice gives linearity; no new integral
    interchange or joint vector continuity of the test topology
    is assumed. The selected field witnesses remain private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing
  CurrentCoefficientNorms CurrentSpaces SmoothFunctionSpaceUP SmoothFunctionSpaceLaws CurrentHomotopyUP
  CurrentHomotopyTransgressionUP CurrentHomotopyTransgressionLocal CurrentHomotopyTransgressionField
  MeasureIntegralUniqueness MeasureSubsetIntegral LebesgueScalarMeasure RealMetricBackground SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTransgressionExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation F := (@current_smooth_space R h2 nu V hV (1+j)).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU j).
Local Notation I := (`[0,1]:set (real_line_metric R)).
Local Notation Integrand := (@current_homotopy_transgression_integrand R h2 n nu j A U V f g h hHomotopy).

(** Source for [current_homotopy_transgression_exists]: the
    original form integral defines a genuine linear operator
    from smooth (j+1)-forms on V to smooth j-forms on U,
    supporting Federer 4.1.9, p. 363. The proof uses
    compact localizations only; no compact support or properness
    of the homotopy, and no extra analytic hypothesis, is required. *)
Theorem current_homotopy_transgression_exists:
  exists K:Hom F E,@is_current_homotopy_transgression R h2 n nu j A U V f g h hHomotopy K.
Proof.
have[K hK]:=choice (@current_homotopy_transgression_field_exists R h2 n nu j A U V f g h hHomotopy).
have hLinear:linear K.
  move=>c psi chi;apply:(smooth_function_extensional hE)=>x hx.
  have[L [W [hW [hWx [hWU hL]]]]]:=
    @current_homotopy_transgression_local R h2 n nu j A U V f g h hHomotopy x hx.
  have hCompare omega:ev (K omega) x=ev (L omega) x.
    apply:pairing_ext=>eta.
    have hEqual:=measure_integral_unique (@hK omega x hx eta) (@hL omega x hWx eta).
    by injection hEqual.
  rewrite (hCompare (c*:psi+chi)) (hom_linear L).
  rewrite !(@smooth_function_evaluation_linear R (R_n R n) (A_m (R_n R n) R^o j)
    (inner_norm (@euclidean_inner_productP R n)) (@current_form_comass R h2 n j)
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (@current_form_comass_real_norm R h2 n j)
    U E ev hE).
  by rewrite (hCompare psi) (hCompare chi).
exists (@HomMap R F E K (introT (asboolP _) hLinear)).
exact:hK.
Qed.
End CurrentHomotopyTransgressionExistence.
