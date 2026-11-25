(** Federer (1969), 2.10.39, printed p. 199: extend the printed
    positive-width box subdivision to zero widths by arbitrarily small
    positive side enlargements. This retains the exact constant and does not
    add a nondegeneracy premise to the measure comparison. All covering
    bounds remain at a fixed cutoff until the later final-supremum argument.
    Source context: PositiveRectangularSphericalCover.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBoxUP FinitePrefixes HausdorffMeasureUP HausdorffDiameterCost
  MetricScaleEnvelopeUP MetricScaleEnvelopeLaws PositiveRectangularSphericalCover
  FiniteProductEnlargement ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectangular_spherical_cutoff_bound]: supporting
    box estimate of 2.10.39, p. 199,
    including degenerate sides omitted by the printed
    positive-width preliminary argument. The strict mesh
    margin permits positive enlargements inside the cutoff. *)
Theorem rectangular_spherical_cutoff_bound (R : realType) n p
    (hp : (p<n)%N) origin axis (c : 'I_n -> R) Q (d : R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  @is_euclidean_rectangular_box R n origin axis c Q ->
  (forall i j : 'I_n, (i<=j)%N -> c j<=c i) ->
  Num.sqrt n%:R*c (Ordinal hp)<d ->
  is_metric_scale_envelope
    (fun j : @positive_closed_metric_balls R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]=>val j)
    (fun j=>hausdorff_diameter_cost p.+1 (val j)) d%:E nu ->
  (nu Q<=(hausdorff_normalisation R p.+1*(Num.sqrt n%:R)^+p.+1*2^+p*
    \prod_(i<p.+1) family_prefix hp c i)%:E)%E.
Proof.
move=> hQ hsort hcap hn.
pose s : R := Num.sqrt n%:R.
pose a : R := hausdorff_normalisation R p.+1*s^+p.+1*2^+p.
have hn0 : (0<n)%N := leq_ltn_trans (leq0n p) hp.
have hs : 0<s by rewrite /s sqrtr_gt0 ltr0n.
pose cap := (d-s*c (Ordinal hp))/s.
have hcap0 : 0<cap by rewrite /cap divr_gt0 // subr_gt0.
rewrite leNgt; apply/negP=> hbad.
have [q [hbq hqn]] := @extended_rationals_order_dense R
  (a*\prod_(i<p.+1) family_prefix hp c i)%:E (nu Q) hbad.
have hb : a*\prod_(i<p.+1) family_prefix hp c i<ratr q := hbq.
have [e [he [hecap hcost]]] := @finite_width_product_small_enlargement R
  (Finite.clone 'I_p.+1 _) (family_prefix hp c) a cap (ratr q) hcap0 hb.
pose ce i := c i+e.
pose Qe := [set x : inner_metric_space (@euclidean_inner_productP R n) |
  forall i, 0<=euclidean_inner_product (x-origin) (axis i)<=ce i].
have hQe : is_euclidean_rectangular_box origin axis ce Qe.
  constructor.
  - exact: euclidean_box_orthonormal_law hQ.
  - move=> i; have hc := euclidean_box_width_nonnegative_law hQ i; rewrite /ce; lra.
  - by move=> x; split.
have hsub : Q `<=` Qe.
  move=> x hx i; have /andP [hlo hhi] := (proj1 (euclidean_box_carrier_law hQ x) hx) i.
  rewrite /ce; apply/andP; split=> //; lra.
have hse (i j : 'I_n) : (i<=j)%N -> ce j<=ce i.
  move=> hij; rewrite /ce lerD2r; exact: hsort i j hij.
have hpe : 0<ce (Ordinal hp).
  have hc := euclidean_box_width_nonnegative_law hQ (Ordinal hp); rewrite /ce; lra.
have hcape : Num.sqrt n%:R*ce (Ordinal hp)<d.
  have hmul : s*e<d-s*c (Ordinal hp).
    rewrite mulrC -ltr_pdivlMr //; exact hecap.
  change (is_true (s*(c (Ordinal hp)+e)<d)); rewrite mulrDr; lra.
have hbnd := @positive_rectangular_spherical_cutoff_bound R n p hp origin axis ce Qe d nu
  hQe hse hpe hcape hn.
have hnu : (nu Q<=nu Qe)%E := metric_scale_envelope_mono hn hsub.
have hcostE : ((hausdorff_normalisation R p.+1*(Num.sqrt n%:R)^+p.+1*2^+p*
    \prod_(i<p.+1) family_prefix hp ce i)%:E<(ratr q : R)%:E)%E.
  rewrite lte_fin; exact hcost.
have hfalse := lt_trans hqn (le_lt_trans (le_trans hnu hbnd) hcostE).
by rewrite ltxx in hfalse.
Qed.
