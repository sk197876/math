(** Federer (1969), 4.1.9, p. 363: existence of the
    actual smooth form represented by the original homotopy
    integral. Compatible local Cartesian slices are glued
    using class locality from 3.1.11 and 3.1.20,
    pp. 219–220 and 232–233. Choices stay inside the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormMetric NormBoundedLinearTopology NormDifferentialUP NormRegularity
  NormRegularityOperations NormRegularityLocal InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing
  CurrentCoefficientNorms CurrentSpaces SmoothFunctionSpaceUP CurrentHomotopyUP
  CurrentHomotopyTransgressionUP CurrentHomotopyTransgressionLocal MeasureIntegralUniqueness
  MeasureSubsetIntegral LebesgueScalarMeasure RealMetricBackground SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTransgressionField.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Form := (A_m X R^o j).
Local Notation NF := (@current_form_comass R h2 n j).
Local Notation hNF := (@current_form_comass_real_norm R h2 n j).
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

(** Source for [current_homotopy_transgression_field_exists]:
    the time integral in the second homotopy formula gives
    an actual smooth j-form on the whole original U,
    supporting Federer 4.1.9, p. 363. All local
    integrals use the entire original closed time interval;
    no global support or properness assumption is introduced. *)
Theorem current_homotopy_transgression_field_exists (psi:F):
  exists omega:E,forall x,U x->forall eta:exterior_power X j,
    is_measure_subset_integral (@lebesgue_scalar_measure R) I
      (real_total_integrand (Integrand psi x eta))
      (pairing eta (ev omega x))%:E.
Proof.
have hPoint:forall x:X,exists theta:Form,forall hx:U x,forall eta:exterior_power X j,
    is_measure_subset_integral (@lebesgue_scalar_measure R) I
      (real_total_integrand (Integrand psi x eta)) (pairing eta theta)%:E.
  move=>x;case:(pselect (U x))=>[hx|hNot].
  - have[L [W [hW [hWx [hWU hL]]]]]:=
      @current_homotopy_transgression_local R h2 n nu j A U V f g h hHomotopy x hx.
    exists (ev (L psi) x)=>_ eta;exact:(@hL psi x hWx eta).
  - exists 0=>hx;exact:(False_ind _ (hNot hx)).
have[field hField]:=choice hPoint.
have hSmooth:norm_class_all_orders hNX hNF U field.
  move=>k;apply:(@norm_class_local_representatives R X Form NX NF hNX hNF U field k)=>x hx.
  have[L [W [hW [hWx [hWU hL]]]]]:=
    @current_homotopy_transgression_local R h2 n nu j A U V f g h hHomotopy x hx.
  exists W,(ev (L psi));split=>//;split=>//;split.
  - apply:(@norm_class_open_restriction R X Form NX NF hNX hNF U W (ev (L psi)) k hWU).
    + move=>y hy;apply:(@norm_domain_interior_neighbourhood R X NX hNX W y).2.
      exact:(@open_nbhs_nbhs (real_norm_metric_space hNX) y W (conj hW hy)).
    + exact:(@smooth_function_evaluation_smooth R X Form NX NF hNX hNF U E ev hE (L psi) k).
  - move=>y hy;apply:pairing_ext=>eta.
    have hEqual:=measure_integral_unique (@hL psi y hy eta) (@hField y (hWU y hy) eta).
    by injection hEqual.
have[omega hOmega]:=@smooth_function_evaluation_surjective R X Form NX NF hNX hNF
  U E ev hE field hSmooth.
exists omega=>x hx eta.
rewrite (@hOmega x hx);exact:(@hField x hx eta).
Qed.
End CurrentHomotopyTransgressionField.
