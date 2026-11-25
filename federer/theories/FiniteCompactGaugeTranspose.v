(** Federer (1969), 4.1.7, p. 358: smooth
    multiplication preserves representability. This supporting
    abstract estimate transfers finite original compact-test
    gauges through an actual test operator bounded
    by a nonnegative continuous weight. The weight
    need not be bounded on the whole domain. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP RealMetricBackground FunctionLatticeUP CompactSupportFunctionUP
  CompactSupportProducts DistributionVariationUP DistributionVariationBasic DistributionVariationBoundedExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FiniteCompactGaugeTranspose.
Variable R:realType.
Variable X:topologicalType.
Variables Y0 Y1:lmodType R.
Variables (N0:Y0->R) (N1:Y1->R).
Hypotheses (hN0:is_real_norm N0) (hN1:is_real_norm N1).
Variables E0 E1:lmodType R.
Variables (v0:Hom E0 (GRing.Lmodule.clone R (X->Y0) _))
  (v1:Hom E1 (GRing.Lmodule.clone R (X->Y1) _)).
Variable P:Hom E0 E1.
Variable w:X->R.
Hypothesis hWContinuous:continuous (w:X->real_line_metric R).
Hypothesis hWNonnegative:forall x:X,0<=w x.
Hypothesis hPoint:forall (phi:E0) x,N1 (v1 (P phi) x)<=w x*N0 (v0 phi x).
Variable S:Hom E1 R^o.
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R X)).

(** Source for [finite_compact_gauge_transpose]: each
    compact positive scalar majorant gives a
    finite gauge after the actual test transpose,
    supporting smooth multiplication and the local
    normality equivalences in Federer 4.1.7,
    p. 358. No global weight bound
    or representing density is required. *)
Theorem finite_compact_gauge_transpose:
  (forall f:X->R,Kplus f->exists b:R,is_distribution_variation_value N1 v1 S f b%:E)->
  forall f:X->R,Kplus f->exists b:R,
    is_distribution_variation_value N0 v0 (hom_comp S P) f b%:E.
Proof.
move=>hFinite f hf.
pose g:=fun x:X=>w x*f x.
have hG:Kplus g.
  split;first exact:(@compact_support_continuous_multiplier R X w f hWContinuous hf.1).
  move=>x;exact:mulr_ge0 (hWNonnegative x) (hf.2 x).
have[b hGauge]:=hFinite g hG.
apply:(@distribution_variation_bounded_value_exists R X Y0 N0 hN0 E0 v0 (hom_comp S P)
  f b hf.2)=>phi hPhi.
have hBound:forall x,N1 (v1 (P phi) x)<=g x.
  move=>x;exact:le_trans (@hPoint phi x) (ler_wpM2l (hWNonnegative x) (hPhi x)).
have hAbsolute:=@distribution_variation_absolute_bound R X Y1 N1 hN1 E1 v1 S g b%:E
  hGauge (P phi) hBound.
rewrite lee_fin in hAbsolute.
rewrite hom_compE;exact:le_trans (ler_norm _) hAbsolute.
Qed.
End FiniteCompactGaugeTranspose.
