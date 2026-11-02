(** Federer (1969), 3.2.35, p. 272:
    actual closure replacement for an arbitrary
    convex source with a nonempty interior. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology InnerConvex AffineDilation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_interior_contraction_closure]:
    supporting the closure reduction in Steiner's
    formula, Federer 3.2.35, p. 272.
    An original interior point, actual affine
    continuity and original convexity put every
    strict contraction of the closure in S.
    The original S need not be open or
    measurable; the interior premise belongs only
    to this branch of the later dimension split. *)
Theorem convex_interior_contraction_closure (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (S:set (inner_metric_space hB)) a x (s:R):
  is_inner_convex S ->interior S a ->closure S x ->0<s ->s<1 ->
  S ((1-s)*:a+s*:x).
Proof.
move=>hS ha hx hs0 hs1.
pose k:=s/(1-s).
pose c (u:inner_metric_space hB):=(a+k*:(x-u):inner_metric_space hB).
have hCont:continuous c.
  move=>u; apply:(@continuousD R (inner_metric_space hB) (inner_metric_space hB)
    (fun _=>a) (fun z=>k*:(x-z)) u); first exact:cst_continuous.
  apply:(@continuousZ R (inner_metric_space hB) (inner_metric_space hB)
    (fun _=>k) (fun z=>x-z) u); first exact:cst_continuous.
  apply:(@continuousB R (inner_metric_space hB) (inner_metric_space hB)
    (fun _=>x) (fun z=>z) u); first exact:cst_continuous.
  exact:cvg_id.
have hc:c x=a by rewrite /c subrr scaler0 addr0.
have hNbhs:nbhs x (c @^-1` S).
  apply:hCont; by rewrite hc.
have [u [hu hcu]]:=hx _ hNbhs.
have hDen:1-s!=0 by rewrite gt_eqF // subr_gt0.
have hScalar:(1-s)*k=s by rewrite /k mulrCA mulfV // mulr1.
have hCombination:=hS (c u) u hcu hu s (ltW hs0) (ltW hs1).
have hAlgebra:(1-s)*:c u+s*:u=(1-s)*:a+s*:x.
  by rewrite /c scalerDr scalerA hScalar scalerBr addrA subrK.
by rewrite hAlgebra in hCombination.
Qed.

(** Source for [convex_interior_closure_dilation_cover]:
    every strict homothetic enlargement about
    an original interior point covers closure S,
    supporting Federer 3.2.35, p. 272.
    Inversion of the actual homothety reduces
    this to the proved contraction assertion. *)
Lemma convex_interior_closure_dilation_cover (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (S:set (inner_metric_space hB)) a (t:R):
  is_inner_convex S ->interior S a ->1<t ->
  closure S `<=` (@affine_dilation R V a t) @` S.
Proof.
move=>hS ha ht x hx.
have ht0:0<t:=lt_trans ltr01 ht.
have htN:t!=0 by rewrite gt_eqF.
have hi0:0<t^-1 by rewrite invr_gt0.
have hi1:t^-1<1 by rewrite invf_lt1.
exists (affine_dilation a t^-1 x).
- exact:(convex_interior_contraction_closure hS ha hx hi0 hi1).
- exact:affine_dilation_inverse htN.
Qed.
