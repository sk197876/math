(** Federer (1969), 4.1.7, pp. 356, 359:
    an actual constant multivector density on a
    measurable set. Compact norm integrals use
    the original intersection characteristic formula
    of 2.4.10; no finite total mass is
    imposed on the set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentDensityUP CurrentDensityAction CurrentDensitySealed CurrentMultivectorDual OpenFamilyTopologyMathcomp
  DistributionIntegralFieldUP SmoothCompactSet TopologicalBorel
  PartialFunctionBasic MeasureUP MeasureBasic MeasureFiniteClosure MeasurableFunctionUP MeasurableTotalBasic
  MeasurableTotalCutoff MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCharacteristicDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Z := (exterior_power X m).
Local Notation NZ := (@current_vector_mass R h2 n m).
Local Notation hNZ := (@current_vector_mass_real_norm R h2 n m).
Variable gamma:set X->\bar R.
Hypothesis hm:is_measure gamma.
Hypothesis hB:forall A:set X,@borel_set XT A->measure_measurable gamma A.
Hypothesis hCompact:forall K:set X,@compact XT K->(gamma K < +oo)%E.
Arguments hB : clear implicits.
Arguments hCompact : clear implicits.
Variable A:set X.
Hypothesis hA:measure_measurable gamma A.
Variable z:Z.
Local Notation chi := (@CharacteristicFunction.value R X A).
Local Notation hChi := (@CharacteristicFunction.laws R X A).

(** Source for [current_characteristic_density_integrable]:
    chi_A z is weakly measurable and has
    finite mass integral on every original
    compact set, supporting the in-book
    construction in Federer 4.1.7, p. 359. *)
Lemma current_characteristic_density_integrable:
  @is_locally_integrable_current_density R h2 n m gamma (fun x=>chi x*:z).
Proof.
constructor.
- have hConst:=@measurable_total_constant R X
    [the topologicalType of open_family_topological_space (@current_multivector_weak_laws R n m).1]
    gamma hm z.
  have hCut:=@measurable_total_cutoff R X
    [the topologicalType of open_family_topological_space (@current_multivector_weak_laws R n m).1]
    gamma hm A (fun _=>z) 0 hA hConst.
  have hEq:(fun x=>chi x*:z)=(fun x=>if pselect (A x) then z else 0).
    apply:funext=>x;case:(pselect (A x))=>hx.
    + by rewrite (characteristic_on_set hChi hx) scale1r.
    + by rewrite (characteristic_off_set hChi hx) scale0r.
  by rewrite hEq.
- move=>K.
  pose C:=smooth_compact_carrier K `&` A.
  have hKMeas:=hB (smooth_compact_carrier K)
    (closed_borel_set (compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact K))).
  have hCMeas:=measure_measurable_intersection hm hKMeas hA.
  have hFinite:gamma C \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm C)).
    apply:le_lt_trans (@measure_mono R X gamma hm C (smooth_compact_carrier K) (fun x hx=>hx.1)) _.
    exact:hCompact _ (smooth_compact_is_compact K).
  pose s:=@CharacteristicFunction.value R X C.
  have hs:=@CharacteristicFunction.laws R X C.
  have hI:=@measure_characteristic_integral R X gamma hm C s hs hCMeas.
  rewrite -(fineK hFinite) in hI.
  have hScale:=@real_total_integral_scale R X gamma hm s (fine (gamma C)) (NZ z) hI.
  have hPoint:(fun x=>if pselect (smooth_compact_carrier K x) then NZ (chi x*:z) else 0)=
    (fun x=>NZ z*s x).
    apply:funext=>x;rewrite /s;case:(pselect (smooth_compact_carrier K x))=>hx.
    + case:(pselect (A x))=>ha.
      * by rewrite (characteristic_on_set hChi ha) scale1r (characteristic_on_set hs (conj hx ha)) mulr1.
      * rewrite (characteristic_off_set hChi ha) scale0r (real_seminorm_zero hNZ.1)
          (characteristic_off_set hs (fun hc=>ha hc.2)) mulr0;by [].
    + by rewrite (characteristic_off_set hs (fun hc=>hx hc.1)) mulr0.
  exists (NZ z*fine (gamma C));by rewrite hPoint.
Qed.

(** Source for [current_characteristic_density]: the
    original actual current gamma restricted to A
    with constant vector z, supporting the
    in-book half-line current in Federer
    4.1.7, p. 359. *)
Definition current_characteristic_density:@full_current_space R h2 n m:=
  @CurrentDensity.value R h2 n m gamma hm
    (fun B hOpen=>hB B (open_borel_set hOpen)) (fun x=>chi x*:z)
    current_characteristic_density_integrable.

(** Source for [current_characteristic_density_action]:
    every original test has the exact
    integral of chi_A times its pairing
    with z, supporting Federer 4.1.7,
    pp. 356, 359. *)
Lemma current_characteristic_density_action:
  is_current_density_action gamma (fun x=>chi x*:z) current_characteristic_density.
Proof. exact:CurrentDensity.laws. Qed.
End CurrentCharacteristicDensity.
