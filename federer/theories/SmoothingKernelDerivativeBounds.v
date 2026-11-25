(** Federer (1969), 4.1.2, pp. 346–347:
    every derivative of the actual compact smooth kernel
    has a finite global supremum norm. The existing
    compact-support theorem of 3.1.13 proves the bound;
    the supremum implementation stays opaque. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm NormHigherDifferentialUP
  NormClassHigherUP NormRegularity CompactSupportFunctionUP NormCompactSupportHigherBound
  UniformFunctionNormUP BoundedFunctionNormSealed SmoothingKernelUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_kernel_derivative_supremum_exists]:
    the original finite sup im ||D^i Phi||,
    Federer 4.1.2, pp. 346–347, with
    its actual higher differential and vanishing off
    the original kernel support. *)
Theorem smoothing_kernel_derivative_supremum_exists (R:realType) n
    (phi:R_n R n->R):is_smoothing_kernel phi ->forall k,
  exists (D:R_n R n->@ContinuousMultilinear.space R k (R_n R n) R^o
      (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|)
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R)) (G:R),
    (forall x,has_norm_higher_differential (inner_norm (@euclidean_inner_productP R n))
      (fun j=>@ContinuousMultilinear.evaluation R j (R_n R n) R^o
        (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|)
        (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R))
      (fun j=>@ContinuousMultilinear.norm R j (R_n R n) R^o
        (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|)
        (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R))
      (fun _=>True) phi k x (D x)) /\
    is_uniform_function_norm (fun x=>@ContinuousMultilinear.norm R k (R_n R n) R^o
      (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|)
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R) (D x)) G.
Proof.
move=>hPhi k.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hR:=@scalar_absolute_value_norm R.
pose Z:=fun j=>@ContinuousMultilinear.space R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose ev:=fun j=>@ContinuousMultilinear.evaluation R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose ZN:=fun j=>@ContinuousMultilinear.norm R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose hZ:=fun j=>@ContinuousMultilinear.laws R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose K:=@real_function_support R (real_norm_metric_space hN) phi.
have hZero x:~K x ->phi x=0:=@real_function_zero_off_support R (real_norm_metric_space hN) phi x.
have [D [M [hD [hM [hBound hOff]]]]]:=@norm_compact_support_higher_differential_bound R X R^o
  N (fun t:R^o=>`|t|) hN hR Z ev ZN hZ K phi k (smoothing_kernel_support_compact hPhi)
  hZero (smoothing_kernel_smooth hPhi k).
have hNk:=continuous_multilinear_norm_is_norm hR (hZ k).
have hFinite:exists M:R,0<=M /\ forall x,`|ZN k (D x)|<=M.
  exists M; split; first exact:ltW hM.
  move=>x; rewrite (ger0_norm (real_seminorm_nonnegative hNk.1 (D x))); exact:hBound.
exists D,(BoundedFunctionNorm.value hFinite); split; first exact hD.
exact:BoundedFunctionNorm.laws.
Qed.
