(** Federer (1969), 4.1.2, p. 347: a
    smooth compact scalar kernel has actual smooth
    directional derivatives with the same compact radius
    bound. Existence follows from the previous calculus;
    the support bound follows from locality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  SmoothCompactSet NormClassOneDirectionalField SmoothRawDirectionalDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_scalar_kernel_directional_exists]: the
    original D_j Phi is again a smooth compact
    kernel for the iterated convolution formula of
    Federer 4.1.2, p. 347. The direction
    is arbitrary and may be zero. *)
Theorem compact_scalar_kernel_directional_exists (R:realType) n (psi:R_n R n->R) r v:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) (fun _=>True) psi ->
  (forall z,r<inner_norm (@euclidean_inner_productP R n) z ->psi z=0) ->
  exists (theta:R_n R n->R) (D:R_n R n->Hom (R_n R n) R^o),
    norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (@scalar_absolute_value_norm R) (fun _=>True) theta /\
    (forall z,r<inner_norm (@euclidean_inner_productP R n) z ->theta z=0) /\
    (forall z,has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (fun t:R^o=>`|t|) (fun _=>True) psi z (D z)) /\
    (forall z,D z v=theta z).
Proof.
move=>hPsi hOff.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have [D hD]:=(@norm_class_firstP R X R^o N (fun t:R^o=>`|t|) hN
  (@scalar_absolute_value_norm R) (fun _=>True) psi).1 (hPsi 1%N).
have hActual z:has_norm_differential N (fun t:R^o=>`|t|) (fun _=>True) psi z (D z).
  exact:(norm_class_one_differential hD Logic.I).
exists (fun z=>D z v),D; split.
- exact:(@smooth_raw_directional_derivative R X R^o N (fun t:R^o=>`|t|)
    hN (@scalar_absolute_value_norm R) psi D hPsi hActual v).
- split; last by split.
  pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
    [set z|N (z-0)<=r] (fun _ _=>Logic.I)
    (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN 0 r).
  have hZero z:~smooth_compact_carrier K z ->psi z=0.
    move=>hz; apply:hOff.
    rewrite ltNge; apply/negP=>hNear; apply:hz.
    change (is_true (N (z-0)<=r)); by rewrite subr0.
  have hDZero:=@norm_differential_zero_off_compact R X R^o N (fun t:R^o=>`|t|)
    hN (@scalar_absolute_value_norm R) K psi D hZero hActual.
  move=>z hz.
  have hOutside:~smooth_compact_carrier K z.
    change (~(is_true (N (z-0)<=r))).
    rewrite subr0; apply/negP; by rewrite -ltNge.
  rewrite (hDZero z hOutside); reflexivity.
Qed.
