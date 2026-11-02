(** Supporting convex geometry for Federer (1969), 2.10.4(2), p. 172: the
    closure of an open convex generator is contained in every strict
    dilation of that generator about one of its points. Equivalently, a
    strict contraction of a closure point toward an interior point lies in
    the open set. The proof uses only affine continuity, the defining
    neighbourhood property of closure and convexity. Source context and the
    absence of an identical. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_convex_contraction_closure]: supporting
    homothetic containment for the closed convex family
    comparison in Federer 2.10.4(2), p. 172.
    Perturb the interior endpoint continuously as the
    other endpoint approaches a closure point. This
    statement needs no finite-dimensionality assumption. *)
Theorem open_convex_contraction_closure (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (U : set (inner_metric_space hB)) (a x : inner_metric_space hB) (s : R) :
  open U -> @is_inner_convex R V U -> U a -> closure U x -> 0<s -> s<1 ->
  U ((1-s)*:a+s*:x).
Proof.
move=> ho hc ha hx hs0 hs1.
pose k := s/(1-s).
pose c (u : inner_metric_space hB) := (a+k*:(x-u) : inner_metric_space hB).
have hcont : continuous c.
  move=> u; apply: (@continuousD R (inner_metric_space hB) (inner_metric_space hB)
    (fun _ => a) (fun z => k*:(x-z)) u); first exact: cst_continuous.
  apply: (@continuousZ R (inner_metric_space hB) (inner_metric_space hB)
    (fun _ => k) (fun z => x-z) u); first exact: cst_continuous.
  apply: (@continuousB R (inner_metric_space hB) (inner_metric_space hB)
    (fun _ => x) (fun z => z) u); first exact: cst_continuous.
  exact: cvg_id.
have hcx : c x=a by rewrite /c subrr scaler0 addr0.
have hn : nbhs x (c @^-1` U).
  apply: hcont; rewrite hcx.
  by rewrite openE in ho; exact: ho a ha.
have [u [hu hcu]] := hx _ hn.
have h1s : 1-s!=0 by rewrite gt_eqF // subr_gt0.
have hk : (1-s)*k=s by rewrite /k mulrCA mulfV // mulr1.
have hh := hc (c u) u hcu hu s (ltW hs0) (ltW hs1).
have he : (1-s)*:c u+s*:u=(1-s)*:a+s*:x.
  by rewrite /c scalerDr scalerA hk scalerBr addrA subrK.
by rewrite he in hh.
Qed.
