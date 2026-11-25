(** Federer (1969), 4.1.1, p. 346: support
    of phi(x+c) lies in K-c when phi has
    support in K. This auxiliary compact index
    uses the original norm topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SmoothCompactSet FiniteNormCompactHull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_translate]: the compact
    shifted support bound used for the test
    translations in Federer 4.1.1, p. 346. *)
Definition smooth_compact_translate (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (K:smooth_compact_set hNX (fun _=>True)) (c:X):smooth_compact_set hNX (fun _=>True).
Proof.
refine (@Build_smooth_compact_set R X NX hNX (fun _=>True)
  [set x|smooth_compact_carrier K (x+c)] (fun _ _=>Logic.I) _).
have hEq:[set x:real_norm_metric_space hNX|smooth_compact_carrier K (x+c)]=
  (fun x:real_norm_metric_space hNX=>(x-c:real_norm_metric_space hNX)) @`
    [set x|smooth_compact_carrier K x].
  apply:funext=>x; apply:propext; split.
  - move=>hx; exists (x+c); first exact hx; by rewrite addrK.
  - move=>[y hy <-]; by rewrite /= subrK.
rewrite hEq; apply:continuous_compact (smooth_compact_is_compact K).
apply:continuous_subspaceT; exact:norm_translation_continuous.
Defined.
