(** Federer (1969), 3.3.19, p. 305: expand the actual
    child-disc condition in original polar coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology ring.
From Federer Require Import InnerProductUP Bilinear InnerNorm InnerMetric InnerUnitNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_radial_ball_square]: the actual squared
    distance between the child centre z+t u and x, in terms
    of the actual radial direction (x-z)/|x-z|. This is
    elementary bilinear algebra supporting the original eta_n
    estimate in 3.3.19, p. 305. *)
Theorem inner_radial_ball_square (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B)
    (z u x:inner_metric_space hB) (t:R):
  inner_norm hB u= 1 ->0<inner_norm hB (x-z) ->
  mdist (z+t*:u) x^+2=
    (inner_norm hB (x-z))^+2+t^+2-
    2* t* inner_norm hB (x-z)* B u (inner_unit_normalization hB (x-z)).
Proof.
move=>hu hPositive.
pose d:= inner_norm hB (x-z).
have hNonzero:d!=0 by rewrite gt_eqF.
have hNormalize:d*:inner_unit_normalization hB (x-z)= x-z.
  by rewrite /d /inner_unit_normalization scalerA mulfV // scale1r.
have hInner:B u (x-z)= d* B u (inner_unit_normalization hB (x-z)).
  have hRaw:=congr1 (B u) hNormalize.
  by rewrite (bilZr (inner_bilinear hB)) in hRaw;symmetry.
have hDifference:(z+t*:u)-x= t*:u-(x-z).
  by rewrite opprB addrCA addrA.
have hUnit:B u u= 1 by rewrite -(inner_norm_sqr hB) hu expr1n.
rewrite inner_metric_distanceE (inner_norm_sqr hB ((z+t*:u)-x)) hDifference.
have hExpansion:B (t*:u-(x-z)) (t*:u-(x-z))=
  t^+2*B u u-2*t*B u (x-z)+B (x-z) (x-z).
  rewrite (bilBl (inner_bilinear hB) (t*:u) (x-z))
    (bilBr (inner_bilinear hB) (t*:u) (t*:u) (x-z))
    (bilBr (inner_bilinear hB) (x-z) (t*:u) (x-z))
    !(bilZl (inner_bilinear hB)) !(bilZr (inner_bilinear hB))
    (inner_symmetric hB (x-z) u).
  change (t*(t*B u u)-t*B u (x-z)-(t*B u (x-z)-B (x-z) (x-z))=
    t^+2*B u u-2*t*B u (x-z)+B (x-z) (x-z)).
  ring.
rewrite hExpansion hUnit mulr1 -(inner_norm_sqr hB (x-z)) hInner.
rewrite /d.
ring.
Qed.
