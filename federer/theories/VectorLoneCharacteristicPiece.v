(** Federer (1969), 4.1.7, p. 356:
    measurable restrictions act on the original
    L1 extension of T. This supporting
    characteristic-piece law is 2.4.12,
    pp. 86–88, using the previous norm
    integral and dominated-integrability theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP
  CharacteristicFunctionUP CharacteristicVectorPiece MeasurableNormedFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureLoneNormIntegral MeasureLpNorm MeasureLpMembershipUP
  SummableRealFunctionUP TotalVectorNormIntegrability TotalNormedLone VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [vector_lone_characteristic_piece]:
    chi_A f is in the actual original
    vector L1 class whenever f is,
    supporting Federer 4.1.7, p. 356.
    A may have infinite mass and the
    whole normed target need not be separable. *)
Theorem vector_lone_characteristic_piece (R:realType) (X:choiceType)
    (V:lmodType R) (NV:V->R) (hNV:is_real_norm NV)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X) (s:X->R) (f:X->V):
  is_characteristic_function A s ->measure_measurable mu A ->
  is_measure_lp_function mu 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hNV))) ->
  is_measure_lp_function mu 1 (partial_function_total (fun x=>(s x*:f x:real_norm_metric_space hNV))).
Proof.
move=>hs hA hf.
pose g x:=s x*:f x.
have hNormed:=@measurable_normed_characteristic_piece R X V NV hNV mu hm A s
  (fun x=>(f x:real_norm_metric_space hNV)) hs hA hf.2.1.
pose b:=measure_lp_norm mu NV 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hNV))).
have hBNonnegative:(0<=b)%E:=@measure_lp_norm_nonnegative R X V NV hNV mu 1 _ hm hf.1 hf.2.1.1.
have hBFinite:b \is a fin_num by rewrite (ge0_fin_numE hBNonnegative);exact:hf.2.2.1.
have hOld:=@measure_lone_norm_integral R X V NV hNV mu hm _ hf.
have hTotal:=measure_integral_graph_equivalent
  (@total_vector_norm_power_one_graph R X V NV hNV f) hOld.
change (is_measure_integral mu (real_total_integrand (fun x=>NV (f x))) b) in hTotal.
rewrite -(fineK hBFinite) in hTotal.
have hNewMeas:=@total_vector_norm_integrand_measurable R X V NV hNV mu hm g hNormed.1.
have hDom:forall x,`|NV (g x)|<=NV (f x).
  move=>x;rewrite (ger0_norm (real_seminorm_nonnegative hNV.1 _)) /g.
  case:(pselect (A x))=>hx.
  - by rewrite (characteristic_on_set hs hx) scale1r.
  - rewrite (characteristic_off_set hs hx) scale0r (real_seminorm_zero hNV.1).
    exact:real_seminorm_nonnegative hNV.1 _.
have [c [hValue _]]:=@real_total_dominated_integral R X mu hm
  (fun x=>NV (g x)) (fun x=>NV (f x)) (fine b) hNewMeas hTotal hDom.
exact:(@total_normed_lone_from_norm_integral R X V NV hNV mu hm g c hNormed hValue).
Qed.
