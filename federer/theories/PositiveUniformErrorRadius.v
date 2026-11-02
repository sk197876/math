(** Federer (1969), 3.2.36, p. 272:
    choose a small radius for the uniform
    Steiner tube-volume error bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_uniform_error_radius_exists]:
    elementary scalar support for compact-convex
    volume continuity in Federer 3.2.36,
    p. 272. Given a nonnegative finite
    common volume bound C and positive error
    e, a positive cutoff at most one
    makes the product cutoff*C strictly less
    than e. This is an auxiliary existence
    proof, not a selected global radius. *)
Lemma positive_uniform_error_radius_exists (R:realType) (C e:R):
  0<=C ->0<e ->exists d:R,0<d /\d<=1 /\d*C<e.
Proof.
move=>hC he.
have hC1:0<C+1 by lra.
pose d:=Num.min 1 (e/(C+1)).
have hd:0<d by rewrite /d lt_min ltr01 divr_gt0.
have hd1:d<=1 by rewrite /d ge_min lexx.
have hdRatio:d<=e/(C+1) by rewrite /d ge_min lexx orbT.
have hProduct:d*(C+1)<=e by move:hdRatio; rewrite ler_pdivlMr //.
exists d; split=>//; split=>//; nra.
Qed.
