(** Private existence proof for the angular B function in
    Federer (1969), 3.2.13, pp. 250–251. The defining
    sphere integral is proved finite and positive before sealing. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EulerBetaUP EulerGamma GammaAngularEvaluation GaussianProductIntegrand HausdorffMeasure
  PartialFunctionUP MeasureSubsetIntegral MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euler_beta_exists]: proved existence of B
    with its independent defining angular integral, Federer 3.2.13,
    p. 250. This witness is private to the opaque sealing
    module and the assumptions audit. *)
Theorem euler_beta_exists (R:realType) m:
  (0<m)%N ->exists B:partial_function (R_n R m) R,is_euler_beta B.
Proof.
move=>hm.
pose rel (z:R_n R m) (a:R):=(forall j,0<z j) /\
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1]
    (real_total_integrand (gaussian_angular_integrand z)) (2*a)%:E.
have hu z a b:rel z a ->rel z b ->a=b.
  move=>[_ ha] [_ hb]; have he:=EFin_inj (measure_integral_unique ha hb); lra.
pose B:=@Build_partial_function (R_n R m) R rel hu.
have hPositiveWitness (z:R_n R m) (hz:forall j,0<z j):
    exists a,0<a /\rel z a.
  pose q:=(\prod_j euler_gamma (hz j))/euler_gamma (positive_coordinate_sum hm hz).
  have hNum:0<\prod_j euler_gamma (hz j).
    apply:prodr_gt0=>j _; exact:euler_gamma_positive.
  have hDen:=euler_gamma_positive (positive_coordinate_sum hm hz).
  exists q; split; first exact:divr_gt0 hNum hDen.
  split=>//.
  have hI:=@gamma_angular_integral_evaluation R m z hz hm.
  have hValue:2*q= 2*(\prod_j euler_gamma (hz j))/euler_gamma (positive_coordinate_sum hm hz).
    rewrite /q; ring.
  by rewrite hValue.
exists B; constructor.
- by move=>z a.
- move=>z hz; have [a [ha hRel]]:=hPositiveWitness z hz; by exists a.
- move=>z a hRel.
  have [b [hb hB]]:=hPositiveWitness z hRel.1.
  by rewrite (hu z a b hRel hB).
Qed.
