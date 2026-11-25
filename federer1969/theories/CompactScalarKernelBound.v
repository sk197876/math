(** Federer (1969), 4.1.2, p. 347: a
    smooth scalar kernel vanishing outside a bounded ball
    has a finite global bound. The earlier compact
    ball and compact continuity theorems supply it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClassOneUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness FiniteNormEquivalence NormCompactFunctionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_scalar_kernel_bound_exists]: every
    continuous scalar kernel supported in a fixed ball
    has a positive finite uniform bound, supporting
    Federer 4.1.2, p. 347. Dimension
    zero and an empty bounding ball are included. *)
Theorem compact_scalar_kernel_bound_exists (R:realType) n (psi:R_n R n->R) r:
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|)
    (fun _=>True) psi ->
  (forall z,r<inner_norm (@euclidean_inner_productP R n) z ->psi z=0) ->
  exists M:R,0<M /\ forall z,`|psi z|<=M.
Proof.
move=>hPsi hOff.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose K:= [set z:X|N (z-0)<=r].
have hCompact:@compact (real_norm_metric_space hN) K.
  exact:(@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN 0 r).
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X R^o N (fun t:R^o=>`|t|)
  hN (@scalar_absolute_value_norm R) (fun _=>True) K psi hCompact (fun _ _=>Logic.I) hPsi.
exists M; split; first exact hM.
move=>z; case:(pselect (K z))=>[hz|hz]; first exact:hBound z hz.
have hLarge:r<N z.
  rewrite ltNge; apply/negP=>hSmall; apply:hz.
  change (is_true (N (z-0)<=r)); by rewrite subr0.
by rewrite (hOff z hLarge) normr0; exact:ltW hM.
Qed.
