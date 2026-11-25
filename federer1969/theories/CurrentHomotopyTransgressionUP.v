(** Federer (1969), 4.1.9, p. 363: independent specification
    of the form homotopy operator. Its original time integral
    is written first with the actual smooth pullback and the
    P/Q exterior product of 4.1.8, p. 362. The velocity
    formula is a consequence of the actual differential law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanCartesianMap
  EuclideanOneCoordinate ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing
  CurrentSpaces CurrentCartesianDomain CurrentCartesianVectorProduct SmoothFunctionSpaceUP
  SmoothFunctionSpaceLaws SmoothFormPullbackSealed ConvexMetricSegment CurrentHomotopyUP
  CurrentHomotopyDomain MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  LebesgueScalarMeasure RealMetricBackground SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTransgressionUP.
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
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation F := (@current_smooth_space R h2 nu V hV (1+j)).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation Pull := (@SmoothFormPullback.operator R h2 (1+n)%N nu (1+j) AU V hAU hV h image hHomotopy.2).
Local Notation pv := (@current_smooth_value R h2 (1+n)%N AU hAU (1+j)).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation velocity := (exterior_first_inclusion (R_n R 1%N) (v-u)).
Local Notation P := (@current_cartesian_vector_product R 1%N n 1%N j).
Local Notation I := (`[0,1]:set (real_line_metric R)).

(** Source for [current_homotopy_transgression_integrand]: the
    original integral pairs the pulled-back form with the
    time velocity wedged with the original spatial multivector,
    Federer 4.1.9, p. 363, using the segment-slice formula
    immediately preceding it in 4.1.8, p. 362. *)
Definition current_homotopy_transgression_integrand (psi:F) x (eta:exterior_power X j) t:R:=
  pairing (P velocity eta) (pv (Pull psi) (euclidean_block_join (metric_segment_point u v t,x))).

(** Source for [is_current_homotopy_transgression]: the literal
    interval integral characterises the linear smooth form
    homotopy operator, Federer 4.1.9, p. 363. Neither
    existence nor a homotopy identity is assumed here. Every
    actual smooth target form is admitted, with no support
    or properness condition on h. *)
Definition is_current_homotopy_transgression (K:Hom F E):Prop:=
  forall psi x,U x->forall eta:exterior_power X j,
    is_measure_subset_integral (@lebesgue_scalar_measure R) I
      (real_total_integrand (current_homotopy_transgression_integrand psi x eta))
      (pairing eta (ev (K psi) x))%:E.

(** Source for [current_homotopy_transgression_unique]: the
    original integral law determines a unique smooth form
    operator, supporting Federer 4.1.9, p. 363. The
    proof uses only scalar integral uniqueness and the
    original nondegenerate exterior pairing. *)
Theorem current_homotopy_transgression_unique (K L:Hom F E):
  is_current_homotopy_transgression K->is_current_homotopy_transgression L->K=L.
Proof.
move=>hK hL;apply:hom_ext=>psi.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 n U hU j))=>x hx.
apply:pairing_ext=>eta.
have hEqual:=measure_integral_unique (@hK psi x hx eta) (@hL psi x hx eta).
by injection hEqual.
Qed.
End CurrentHomotopyTransgressionUP.
