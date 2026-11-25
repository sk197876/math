(** Federer (1969), 4.1.19, p. 377: represent
    the scalar components of a bounded L1
    functional by the earlier scalar Radon duality.
    The raw carrier retains total values; the
    scalar theorem concerns the corrected total-domain
    space in 2.5.7, p. 98. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric
  MeasurableRealNormed MeasureUP RadonMeasureUP
  PartialFunctionBasic MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP MeasureLpNorm MeasureLpMembershipUP MeasureExponentDomain
  FunctionLatticeSeminormUP TotalScalarLpUP TotalScalarLpClosure
  TotalScalarLpFiniteSeminorm RealLatticeDensityUP
  SummableFieldSealed SummableFieldLaws SummableFieldIntegral
  SummableFieldRepresentation RadonBoundedLoneDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ScalarFunctional.
Variable R : realType.
Variable X : topologicalType.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation N := (fun t : R => `|t|%R).
Local Notation hN := (scalar_absolute_value_norm R).
Local Notation W := (@SummableField.space R X R^o N hN mu hm).
Local Notation value := (@summable_field_value R X R^o N hN mu hm).
Local Notation size := (@summable_field_size R X R^o N hN mu hm).
Local Notation Q := (@total_scalar_lp R X mu 1).

(** Source for [summable_scalar_functional_total_extension]:
    express the raw L1 functional in the
    total-domain scalar language of 2.5.7, p. 98,
    used in Federer 4.1.19, p. 377.
    The resulting functional is linear on the
    original L1 domain and keeps the exact bound. *)
Theorem summable_scalar_functional_total_extension
    (F : Hom W R^o) (c : R)
    (hBound : forall w, `|F w| <= c*size w) :
  exists A : (X -> R) -> R,
    (forall w, A (value w) = F w) /\
    is_linear_functional_on_functions Q A /\
    forall f, Q f -> `|A f| <= c*finite_total_scalar_lp_norm mu 1 f.
Proof.
have hRepresent (f : X -> R) (hf : Q f) :
    exists w : W, value w = f.
  have hVector :=
    (@total_scalar_lp_finite_equivalence R X mu hm 1 f).1 hf.
  have [w [hValue hSize]] :=
    @summable_total_field_representative R X R^o N hN mu hm f hVector.
  by exists w.
pose A (f : X -> R) : R :=
  match pselect (Q f) with
  | left hf => F (projT1 (cid (@hRepresent f hf)))
  | right _ => 0
  end.
have hAt (f : X -> R) (hf : Q f) (w : W) (hValue : value w = f) :
    A f = F w.
  rewrite /A; case: pselect=> [hMem|hNot]; last exact: False_ind _ (hNot hf).
  have hChosen : value (projT1 (cid (@hRepresent f hMem))) = f.
    exact: (projT2 (cid (@hRepresent f hMem))).
  have hEqual : projT1 (cid (@hRepresent f hMem)) = w.
    apply: (@summable_field_value_injective R X R^o N hN mu hm).
    exact: (eq_trans hChosen (esym hValue)).
  by rewrite hEqual.
have hValueMem (w : W) : Q (value w).
  apply: (@total_scalar_lp_finite_equivalence R X mu hm 1 (value w)).2.
  exact: (@summable_field_lone R X R^o N hN mu hm w).
exists A; split.
- move=> w; exact: (@hAt (value w) (hValueMem w) w erefl).
split.
- split.
  + move=> f g hf hg.
    have [u hu] := @hRepresent f hf.
    have [v hv] := @hRepresent g hg.
    have hSum := @total_scalar_lp_add R X mu hm 1 f g hf hg.
    have hValues : value (u+v)%R = (fun x => f x+g x).
      by rewrite (@summable_field_value_add R X R^o N hN mu hm) hu hv.
    rewrite (@hAt _ hSum (u+v)%R hValues) linearD.
    by rewrite (@hAt f hf u hu) (@hAt g hg v hv).
  + move=> a f hf.
    have [u hu] := @hRepresent f hf.
    have hScale := @total_scalar_lp_scale R X mu hm 1 a f hf.
    have hValues : value (a*:u)%R = (fun x => a*f x).
      by rewrite (@summable_field_value_scale R X R^o N hN mu hm) hu.
    rewrite (@hAt _ hScale (a*:u)%R hValues) linearZ.
    by rewrite (@hAt f hf u hu).
- move=> f hf.
  have [w hw] := @hRepresent f hf.
  rewrite (@hAt f hf w hw).
  have hSize : size w = finite_total_scalar_lp_norm mu 1 f.
    have hExact : (size w)%:E =
        (finite_total_scalar_lp_norm mu 1 f)%:E.
      rewrite (@summable_field_size_exact R X R^o N hN mu hm)
        (@finite_total_scalar_lp_norm_exact R X mu hm 1 f hf).
      change (measure_lp_norm mu N 1 (partial_function_total (value w)) =
        measure_lp_norm mu N 1 (partial_function_total f)).
      by rewrite hw.
    by injection hExact.
  by rewrite -hSize; exact: hBound.
Qed.

(** Source for [summable_scalar_radon_functional_representation]:
    the scalar representation used for the coefficients
    in Federer 4.1.19, p. 377, with
    the original Radon measure and unchanged pointwise
    bound. This includes the zero measure and
    an original open domain of infinite measure. *)
Theorem summable_scalar_radon_functional_representation
    (hr : is_radon_measure mu) (F : Hom W R^o) (c : R) :
  0 <= c -> (forall w, `|F w| <= c*size w) ->
  exists k : X -> R,
    is_measure_measurable_function mu (total_scalar_function k) /\
    (forall x, `|k x| <= c) /\
    forall w, is_measure_integral mu
      (real_total_integrand (fun x => value w x*k x)) (F w)%:E.
Proof.
move=> hC hBound.
have [A [hA [hLinear hABound]]] :=
  @summable_scalar_functional_total_extension F c hBound.
have [k [hK hCap]] :=
  @radon_bounded_lone_density R X mu hm hr A c hC hLinear hABound.
exists k; split; first exact: hK.1.
split; first exact: hCap.
move=> w.
have hMem : Q (value w).
  apply: (@total_scalar_lp_finite_equivalence R X mu hm 1 (value w)).2.
  exact: (@summable_field_lone R X R^o N hN mu hm w).
have hIntegral := hK.2 (value w) hMem.
by rewrite hA in hIntegral.
Qed.
End ScalarFunctional.
