(** Federer (1969), 4.1.7, pp. 355–358, reused
    in 4.1.18, pp. 374–377: every continuous
    actual multivector field is weakly measurable and
    locally mass-integrable for a Radon measure on
    the original open domain.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormClassZeroWhole NormCompactFunctionBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentCoefficientNorms CurrentDomain CurrentMultivectorDual
  CurrentDensityNormMeasurable OpenCurrentDensityUP MeasureUP RadonMeasureUP
  RadonBorelRegularity MeasureAlmostBasic PartialFunctionBasic PartialFunctionPreimages MeasurableFunctionUP
  MeasurableCompactNormIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_continuous_open_density_integrable]:
    the original local mass-integrability requirement
    of 4.1.7, p. 356, follows from continuity,
    supporting the actual smoothed density and L1
    approximation in 4.1.18, pp. 374–377.
    No global norm bound or finite total measure
    is imposed. *)
Theorem current_continuous_open_density_integrable (R:realType)
    (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (gamma:set (current_domain R n U)->\bar R)
    (hGamma:is_measure gamma) (hRadon:is_radon_measure gamma)
    (xi:current_domain R n U->exterior_power (R_n R n) m):
  continuous (fun x:current_domain R n U=>
    (xi x:real_norm_metric_space (@current_vector_mass_real_norm R h2 n m))) ->
  @is_locally_integrable_open_current_density R h2 n m U gamma xi.
Proof.
move=>hXi.
pose UT:=current_domain R n U.
pose V:=exterior_power (R_n R n) m.
pose VN:=@current_vector_mass R h2 n m.
pose hVN:=@current_vector_mass_real_norm R h2 n m.
pose VT:=real_norm_metric_space hVN.
have hMeas:is_measure_measurable_function gamma
    (partial_function_total (fun x:UT=>(xi x:VT))).
  constructor.
  - rewrite partial_function_total_domain;exact:measure_almost_everywhere_true hGamma.
  - move=>O hO;rewrite partial_function_total_preimage.
    apply:(@radon_open_measurable R UT gamma hRadon (xi @^-1` O)).
    exact:((@continuousP UT VT xi).1 hXi O hO).
split.
- exact:(@current_density_weak_topology_measurable R h2 n m UT gamma hGamma xi hMeas).
- move=>K hK.
  have hImage:compact (xi @` K:set VT).
    apply:continuous_compact hK;exact:continuous_subspaceT hXi.
  have hIdentity:continuous (fun v:VT=>v) by move=>v;exact:cvg_id.
  have [M [hM hBound]]:=@norm_class_zero_compact_bounded R V V VN VN hVN hVN
    setT (xi @` K) (fun v=>v) hImage (fun _ _=>Logic.I)
    (norm_continuous_whole_class_zero hIdentity).
  apply:(@measurable_compact_norm_integral R UT V VN hVN gamma hGamma hRadon
    xi K M hMeas hK (ltW hM))=>x hx.
  apply:hBound;by exists x.
Qed.
