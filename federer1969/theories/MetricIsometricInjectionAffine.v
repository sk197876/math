(** Federer (1969), 3.2.36, p. 273: an arbitrary distance-
    preserving injection between real inner-product spaces has an
    orthogonal linear part. This proves the needed classification
    instead of assuming membership in a packaged affine isometry group. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology ring lra.
From Federer Require Import RealMetricBackground InnerProductUP InnerProductLaws InnerNorm InnerMetric InnerWeightedVariance Bilinear InnerPairingPreserverLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_isometric_injection_linear_part]: the affine
    structure behind the assertion about isometric injections in Federer
    3.2.36, p. 273, using the inner-product laws of 1.7.1--2,
    p. 28. Subtracting f(0), polarizing the preserved distances and
    expanding the squared norm of the additive and scalar residuals
    proves linearity and orthogonality. No surjectivity, finite dimension
    or preassigned linearity hypothesis is imposed on the original f. *)
Theorem metric_isometric_injection_linear_part (R:realType) (V W:lmodType R)
    (B:V->V->R) (C:W->W->R) (hB:is_inner_product B) (hC:is_inner_product C) (f:V->W):
  (forall x y,@mdist R (inner_metric_space hC) (f x) (f y)=
    @mdist R (inner_metric_space hB) x y) ->
  linear (fun x=>f x-f 0) /\forall x y,C (f x-f 0) (f y-f 0)=B x y.
Proof.
move=>hMetric.
pose g:=fun x:V=>f x-f 0.
have hNorm x:inner_norm hC (g x)=inner_norm hB x.
  have h:=hMetric x 0; by rewrite !inner_metric_distanceE subr0 in h.
have hDifference x y:inner_norm hC (g x-g y)=inner_norm hB (x-y).
  have hEq:g x-g y=f x-f y by rewrite /g opprB addrA subrK.
  rewrite hEq; exact:hMetric x y.
have hInner x y:C (g x) (g y)=B x y.
  have h:=congr1 (fun z:R=>z^+2) (hDifference x y).
  rewrite (@inner_difference_norm_square R W C hC) (@inner_difference_norm_square R V B hB)
    !hNorm in h.
  have hCancel (a b u v:R):a+b-2*u=a+b-2*v ->u=v by move=>hFlat; lra.
  exact:hCancel h.
split; last exact:hInner.
exact:(@inner_pairing_preserver_linear R V W B C hB hC g hInner).
Qed.
