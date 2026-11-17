(** Federer (1969), 3.4.12, p. 339: apply the real
    component theorem to the actual underlying real coordinates.
    Bounded linear coordinate changes preserve finite real analytic
    equation systems. Reuse analytic composition and the original
    set-germ preimage theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormLinearDomainLaws NormAnalyticUP NormAnalyticLinear NormAnalyticOperations
  FiniteAnalyticVarietyUP AnalyticVarietyGermUP SetGermUP SetGermContinuousPreimage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [finite_analytic_variety_linear_preimage]: bounded
    real linear coordinates retain the actual finite defining
    equations, supporting the real-case component argument explicitly
    permitted in 3.4.12, p. 339. *)
Theorem finite_analytic_variety_linear_preimage (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (P:Hom X Y) (U S:set Y):
  norm_bounded_linear NX NY P ->is_finite_analytic_variety hNY U S ->
  is_finite_analytic_variety hNX (P @^-1` U) (P @^-1` S).
Proof.
move=>hP [hOpen [I [f [hF hZero]]]].
have hContinuous:=@norm_bounded_linear_continuous R X Y NX NY hNX hNY P hP.
have hU y (hy:U y):norm_domain_interior NY U y.
  have hNear:=hOpen;rewrite openE in hNear.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY U y).2 (hNear y hy).
have hA x (hx:U (P x)):norm_domain_interior NX (P @^-1` U) x.
  exact:(@norm_bounded_linear_preimage_interior R X Y NX NY hNX P U x hP (hU _ hx)).
have hProjection:=@norm_bounded_linear_analytic R X Y NX NY hNX hNY (P @^-1` U) hA P hP.
split.
- exact:(@open_comp (real_norm_metric_space hNX) (real_norm_metric_space hNY)
    P U (fun x _=>hContinuous x) hOpen).
- exists I,(fun i x=>f i (P x));split.
  + move=>i;exact:(@norm_analytic_compose_on R X Y R^o NX NY (fun t:R^o=>`|t|) hNX hNY
      (@scalar_absolute_value_norm R) (P @^-1` U) U P (f i) (fun x hx=>hx) hProjection (hF i)).
  + move=>x;exact:hZero (P x).
Qed.
(** Source for [analytic_variety_germ_linear_preimage]: the original
    variety-germ equality transports through the same continuous
    real coordinate map, supporting 3.4.12, p. 339. Centres
    and actual representatives are retained. *)
Theorem analytic_variety_germ_linear_preimage (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (P:Hom X Y) (a:X) (b:Y) (S:set Y):
  norm_bounded_linear NX NY P ->P a=b ->
  @is_analytic_variety_germ R Y NY hNY b
    (@set_germ (Topological.clone (real_norm_metric_space hNY) _) b S) ->
  @is_analytic_variety_germ R X NX hNX a
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a (P @^-1` S)).
Proof.
move=>hP hCentre [U [H [hb [hH hGerm]]]].
have hPre:=@finite_analytic_variety_linear_preimage R X Y NX NY hNX hNY P U H hP hH.
have hContinuous:=@norm_bounded_linear_continuous R X Y NX NY hNX hNY P hP.
have hEquality:=@set_germ_continuous_preimage_equality
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) P a b H S
  hContinuous hCentre hGerm.
exists (P @^-1` U),(P @^-1` H);split.
- change (U (P a));by rewrite hCentre.
- by split.
Qed.
