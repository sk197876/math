(** Private existence proof for Federer (1969), 2.10.43, printed p. 201, at
    any nonnegative Lipschitz bound. A positive bound is reduced to one by
    target scaling; the already proved maximal-graph extension is scaled
    back. At bound zero the original map is constant on its source; an empty
    source is extended by zero. These cases make the printed initial
    normalisation explicit. The witness will be hidden by opaque module
    ascription. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP
  KirszbraunExtensionUP EuclideanTargetScaling NonexpandingExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_bound_kirszbraun_extension_exists]: supporting
    zero-bound case of the normalisation in 2.10.43,
    p. 201. The original map is constant on
    a nonempty source; an empty source permits the
    constant zero extension. No division by zero occurs. *)
Lemma zero_bound_kirszbraun_extension_exists (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) :
  is_metric_lipschitz_bound S f 0 -> exists g, is_kirszbraun_extension S f g 0.
Proof.
move=> [_ hbound].
case: (pselect (S !=set0))=> [[x0 hx0]|hempty].
- exists (fun _=>f x0); constructor.
  - move=> x hx; have hh := hbound x0 x hx0 hx; rewrite mul0r in hh.
    have hz : mdist (f x0) (f x)=0 by apply/eqP; rewrite eq_le hh (mdist_ge0 _ _).
    exact: mdist_positivity hz.
  - split; first exact: lexx.
    by move=> x y _ _; rewrite mdistxx mul0r.
- exists (fun _=>0); constructor.
  - move=> x hx; exfalso; apply: hempty; by exists x.
  - split; first exact: lexx.
    by move=> x y _ _; rewrite mdistxx mul0r.
Qed.

(** Source for [kirszbraun_extension_exists]: direct existence
    assertion in 2.10.43, p. 201, for an
    arbitrary supplied nonnegative bound. Positive
    bounds are normalised and restored; zero bounds,
    empty sources and zero-dimensional spaces are included. *)
Theorem kirszbraun_extension_exists (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (L : R) :
  is_metric_lipschitz_bound S f L -> exists g, is_kirszbraun_extension S f g L.
Proof.
move=> hSf; case: (eqVneq L 0)=> [hL0|hL0].
- rewrite hL0 in hSf *; exact: zero_bound_kirszbraun_extension_exists hSf.
- have hL : 0<L by rewrite lt_neqAle eq_sym hL0 hSf.1.
  pose f1 x := L^-1*:f x.
  have hf1 : is_metric_lipschitz_bound S f1 1.
    have hh := @euclidean_scaled_lipschitz_bound R m n S f L L^-1 hSf.
    have hi : 0<=L^-1 by rewrite invr_ge0; exact: ltW hL.
    by rewrite (ger0_norm hi) mulVf // in hh.
  have [g1 hg1] := @nonexpanding_total_extension_exists R m n S f1 hf1.
  pose g x := L*:g1 x.
  exists g; constructor.
  - move=> x hx; rewrite /g (@kirszbraun_extension_agreement_law R m n S f1 g1 1 hg1 x hx).
    by rewrite /f1 scalerA mulfV // scale1r.
  - have hh := @euclidean_scaled_lipschitz_bound R m n setT g1 1 L (kirszbraun_extension_bound_law hg1).
    by rewrite (ger0_norm (ltW hL)) mulr1 in hh.
Qed.
