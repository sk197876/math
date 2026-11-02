(** Federer (1969), 3.1.21, p. 234: the normal cone is closed
    and convex, in every inner-product space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerNorm InnerMetric
  OrthonormalFamilies InnerCoordinateContinuity InnerConvex TangentConeUP NormalConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Normals.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Local Notation N := (inner_norm hB).
Local Notation M := (inner_metric_space hB).

(** Source for [inner_normal_cone_convex]: the asserted convexity
    of Nor(S,a), Federer 3.1.21, p. 234, from bilinearity and
    nonnegative convex-combination coefficients. *)
Lemma inner_normal_cone_convex S a : is_inner_convex (inner_normal_cone N B S a).
Proof.
move=>x y hx hy t ht0 ht1 v hv.
rewrite (bilDl (inner_bilinear hB)) !(bilZl (inner_bilinear hB)).
change ((1-t)*B x v+t*B y v<=0).
have hhx:=hx v hv; have hhy:=hy v hv.
nra.
Qed.

(** Source for [inner_normal_cone_closed]: the asserted closedness
    of Nor(S,a), Federer 3.1.21, p. 234, as an arbitrary
    intersection of the closed halfspaces u.v<=0. *)
Lemma inner_normal_cone_closed S a : @closed M (inner_normal_cone N B S a).
Proof.
move=>u hcl v hv.
pose H:set M:=fun x=>B x v<=0.
have hc:closed H.
  have heq:H=(inner_coordinate hB v) @^-1` [set r:R|r<=0].
    apply/seteqP; split=>x.
    - change (B x v<=0 -> inner_coordinate hB v x<=0).
      by rewrite inner_coordinateE.
    - change (inner_coordinate hB v x<=0 -> B x v<=0).
      by rewrite inner_coordinateE.
  rewrite heq; apply: preimage_closed; first by move=>x _; exact: inner_coordinate_continuous x.
  exact: closed_le.
have hsub:inner_normal_cone N B S a `<=` H by move=>x hx; exact: hx v hv.
exact: hc (@closureS M _ _ hsub u hcl).
Qed.
End Normals.
