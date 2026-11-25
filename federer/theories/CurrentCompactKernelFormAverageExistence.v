(** Federer (1969), 4.1.18, p. 374: the
    original compact-kernel form integral defines an actual
    linear smooth-form operator. Local Cartesian slices
    agree by scalar integral uniqueness and glue by
    the previously proved class locality.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormBoundedLinearTopology
  NormDifferentialUP NormRegularity NormRegularityOperations NormRegularityLocal
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanCartesianMap ExteriorGrading AlternatingForms
  AlternatingPairing CurrentSpaces CurrentCoefficientNorms CurrentCartesianDomain
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  CurrentKernelAverageUP CurrentCompactKernelFormAverageUP
  CurrentCompactKernelFormAverageLocal MeasureIntegralUP MeasureIntegralUniqueness
  EuclideanLebesgueDimensions SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactKernelFormAverageExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R q).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R q)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R q)).
Local Notation Form:=(A_m Y R^o j).
Local Notation NF:=(@current_form_comass R h2 q j).
Local Notation hNF:=(@current_form_comass_real_norm R h2 q j).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable U:set Y.
Hypothesis hU:forall x,U x->norm_domain_interior NY U x.
Local Notation AB:=(@euclidean_cartesian_set R n q Full U).
Local Notation hAB:=(@current_cartesian_domain_open R n q Full U hFull hU).
Local Notation F:=(@current_smooth_space R h2 (n+q) AB hAB (0+j)).
Local Notation E:=(@current_smooth_space R h2 q U hU j).
Local Notation ev:=(@current_smooth_value R h2 q U hU j).
Local Notation hE:=(@current_smooth_space_laws R h2 q U hU j).
Variable w:X->R.
Variable S:@current_space R h2 n Full hFull 0%N.
Hypothesis hS:@is_current_kernel_average R h2 n w S.
Variable K:smooth_compact_set hNX Full.
Hypothesis hOff:forall z,~smooth_compact_carrier K z->w z=0.
Local Notation Integrand:=(@current_compact_kernel_form_integrand R h2 n q j U hU w).

(** Source for [current_compact_kernel_form_field_exists]:
    the original parameter integral is a genuine smooth
    form on all of U, supporting Federer 4.1.18,
    p. 374. Empty U requires no point selection
    and every input degree is retained. *)
Theorem current_compact_kernel_form_field_exists (phi:F):
  exists omega:E,forall x,U x->forall eta:exterior_power Y j,
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (Integrand phi x eta))
      (pairing eta (ev omega x))%:E.
Proof.
have hPoint:forall x:Y,exists theta:Form,forall hx:U x,
    forall eta:exterior_power Y j,
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (Integrand phi x eta)) (pairing eta theta)%:E.
  move=>x;case:(pselect (U x))=>[hx|hNot].
  - have [L [W [hW [hWx [hWU hL]]]]]:=
      @current_compact_kernel_form_average_local R h2 n q j U hU w S hS K hOff x hx.
    exists (ev (L phi) x)=>_ eta;exact:(@hL phi x hWx eta).
  - exists 0=>hx;exact:(False_ind _ (hNot hx)).
have [field hField]:=choice hPoint.
have hSmooth:norm_class_all_orders hNY hNF U field.
  move=>k;apply:(@norm_class_local_representatives R Y Form NY NF hNY hNF
    U field k)=>x hx.
  have [L [W [hW [hWx [hWU hL]]]]]:=
    @current_compact_kernel_form_average_local R h2 n q j U hU w S hS K hOff x hx.
  exists W,(ev (L phi));split=>//;split=>//;split.
  - apply:(@norm_class_open_restriction R Y Form NY NF hNY hNF
      U W (ev (L phi)) k hWU).
    + move=>y hy;apply:(@norm_domain_interior_neighbourhood R Y NY hNY W y).2.
      exact:(@open_nbhs_nbhs (real_norm_metric_space hNY) y W (conj hW hy)).
    + exact:(@smooth_function_evaluation_smooth R Y Form NY NF hNY hNF
        U E ev hE (L phi) k).
  - move=>y hy;apply:pairing_ext=>eta.
    have hEqual:=measure_integral_unique (@hL phi y hy eta)
      (@hField y (hWU y hy) eta).
    by injection hEqual.
have [omega hOmega]:=@smooth_function_evaluation_surjective R Y Form NY NF hNY hNF
  U E ev hE field hSmooth.
exists omega=>x hx eta.
rewrite (@hOmega x hx);exact:(@hField x hx eta).
Qed.

(** Source for [current_compact_kernel_form_average_exists]:
    linearity and existence of the original averaged
    smooth form operator, supporting Federer 4.1.18,
    p. 374. A common actual local slice proves
    linearity, so no vector integral in a nonnormed
    smooth space is postulated. *)
Theorem current_compact_kernel_form_average_exists:
  exists A:Hom F E,
    @is_current_compact_kernel_form_average R h2 n q j U hU w A.
Proof.
have [A hA]:=choice current_compact_kernel_form_field_exists.
have hLinear:linear A.
  move=>c phi psi;apply:(smooth_function_extensional hE)=>x hx.
  have [L [W [hW [hWx [hWU hL]]]]]:=
    @current_compact_kernel_form_average_local R h2 n q j U hU w S hS K hOff x hx.
  have hCompare omega:ev (A omega) x=ev (L omega) x.
    apply:pairing_ext=>eta.
    have hEqual:=measure_integral_unique (@hA omega x hx eta)
      (@hL omega x hWx eta).
    by injection hEqual.
  rewrite (hCompare (c*:phi+psi)) (hom_linear L).
  rewrite !(@smooth_function_evaluation_linear R Y Form NY NF hNY hNF U E ev hE).
  by rewrite (hCompare phi) (hCompare psi).
exists (@HomMap R F E A (introT (asboolP _) hLinear)).
exact:hA.
Qed.
End CurrentCompactKernelFormAverageExistence.
