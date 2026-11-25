(** Federer (1969), 4.1.5, pp. 349–350:
    every original norm conclusion of the normalized
    Radon density is retained in the actual abstract
    dual. Exact norm equality transports the proved
    bounds, measurability and compact norm integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP VectorDaniellHypotheses VectorDaniellNormalisationUP
  WeakDualRealisationUP NormalisedWeakDensityCompactNorm PartialFunctionBasic MeasureUP MeasureAlmostUP
  MeasureAlmostBasic RadonMeasureUP MeasurableFunctionUP SummableRealFunctionUP MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WeakDualDensityNormTransport.
Variable R:realType.
Variable X:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Variable J:weak_dual_space hNY->D.
Hypothesis hJ:is_weak_dual_realisation ed DN J.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Variable Q:set (X->Y).
Variable T:(X->Y)->R.
Variable k:X->weak_dual_space hNY.
Hypothesis hk:is_normalised_vector_daniell_density mu Q T k.

(** Source for [weak_dual_density_norm_measurable]:
    the actual dual norm of the original density is
    measurable, supporting Federer 4.1.5, p. 350. *)
Theorem weak_dual_density_norm_measurable:
  is_measure_measurable_function mu (real_total_integrand (fun x=>DN (J (k x)))).
Proof.
have hEq:(fun x=>DN (J (k x)))=(fun x=>dual_norm NY (val (k x))).
  apply:funext=>x; exact:(@weak_dual_realisation_norm R Y NY hNY D ed DN J hJ (k x)).
rewrite hEq; exact:normalised_vector_density_norm_measurable hk.
Qed.

(** Source for [weak_dual_density_unit_norm]:
    ||k(x)||=1 almost everywhere for the original
    actual Y* density, Federer 4.1.5, p. 350. *)
Theorem weak_dual_density_unit_norm:
  measure_almost_everywhere mu [set x|DN (J (k x))= 1].
Proof.
apply:(@measure_almost_everywhere_mono R X mu hm
  [set x|dual_norm NY (val (k x))= 1] [set x|DN (J (k x))= 1] _
  (normalised_vector_density_unit_norm hk))=>x hx.
change (DN (J (k x))= 1).
by rewrite (@weak_dual_realisation_norm R Y NY hNY D ed DN J hJ (k x)).
Qed.

(** Source for [weak_dual_density_unit_bound]:
    the original representing field may take its
    values in the closed unit dual ball, as used
    in Federer 4.1.5, p. 350. *)
Theorem weak_dual_density_unit_bound x:DN (J (k x))<= 1.
Proof.
rewrite (@weak_dual_realisation_norm R Y NY hNY D ed DN J hJ (k x)).
exact:normalised_vector_density_bound hk x.
Qed.

(** Source for [weak_dual_density_compact_norm]:
    compact local norm integrability of the actual
    abstract Y* field, Federer 4.1.5, p. 349. *)
Theorem weak_dual_density_compact_norm:
  is_radon_measure mu ->forall K:set X,compact K ->exists c:R,
    is_measure_subset_integral mu K (real_total_integrand (fun x=>DN (J (k x)))) c%:E.
Proof.
move=>hr K hK.
have[c [hI _]]:=@normalised_weak_density_compact_norm_integral R X Y NY hNY mu hm hr Q T k hk K hK.
have hEq:(fun x=>DN (J (k x)))=(fun x=>dual_norm NY (val (k x))).
  apply:funext=>x; exact:(@weak_dual_realisation_norm R Y NY hNY D ed DN J hJ (k x)).
exists c; by rewrite hEq.
Qed.
End WeakDualDensityNormTransport.
