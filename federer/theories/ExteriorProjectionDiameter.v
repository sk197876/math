(** Federer (1969), 2.10.34, printed p. 197: orthogonal projection does not
    increase the exterior cost zeta of 2.10.3, p. 171. Expand the printed
    use of 1.7.6 through the already proved pointwise exterior projection
    norm bound, without choosing a norm-maximising vector. No relevant
    correction occurs in Federer's working erratum for this corollary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric CoordinateProjection
  ExteriorGrading ExteriorMaps ExteriorMapNormContinuity ExteriorProjectionNorm FiniteExteriorPowers
  ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter ExteriorMeasureGauge HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_exterior_endpoint_norm_bound]: supporting
    endpoint-product contraction in the final display
    of 2.10.34, p. 197. The
    degree is arbitrary, including zero and
    degrees greater than either ambient dimension. *)
Lemma projection_exterior_endpoint_norm_bound (R : realType) (n k m : nat)
    (p : {linear R_n R n -> R_n R k}) (a b : 'I_m -> R_n R n) :
  O_star p -> exterior_difference_norm (p \o a) (p \o b)<=exterior_difference_norm a b.
Proof.
move=> hp.
have he : (fun i=>p (a i)-p (b i))=p \o (fun i=>a i-b i).
  by apply: funext=> i; rewrite /= linearB.
rewrite /exterior_difference_norm /exterior_difference_product /= he -exterior_power_map_e_lambda.
exact: (@exterior_projection_norm_bound R (real_exterior_two_nonzero R)
  (R_n R n) (R_n R k) (@euclidean_inner_product R n) (@euclidean_inner_product R k)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R k) p
  (proj1 (O_star_projection p) hp) m _).
Qed.

(** Source for [projection_extended_exterior_diameter_bound]: supporting
    supremum contraction for the last inequality
    of 2.10.34, p. 197. Choose
    preimages of each finite endpoint family;
    no measurable or continuous choice is assumed. *)
Theorem projection_extended_exterior_diameter_bound (R : realType) (n k m : nat)
    (p : {linear R_n R n -> R_n R k}) (S : set (R_n R n)) :
  O_star p -> (extended_exterior_diameter m (p @` S)<=extended_exterior_diameter m S)%E.
Proof.
move=> hp; apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification m (p @` S))).
- exact: exterior_diameter_nonnegative (extended_exterior_diameter_specification m S).
- move=> a b ha hb.
  have hae i : exists x, S x /\ p x=a i.
    have [x hx he] := ha i; by exists x.
  have hbe i : exists x, S x /\ p x=b i.
    have [x hx he] := hb i; by exists x.
  pose a' i := projT1 (cid (hae i)).
  pose b' i := projT1 (cid (hbe i)).
  have hsa i : S (a' i) := (projT2 (cid (hae i))).1.
  have hsb i : S (b' i) := (projT2 (cid (hbe i))).1.
  have hea : p \o a'=a by apply: funext=> i; exact: (projT2 (cid (hae i))).2.
  have heb : p \o b'=b by apply: funext=> i; exact: (projT2 (cid (hbe i))).2.
  have hh := projection_exterior_endpoint_norm_bound a' b' hp.
  rewrite hea heb in hh.
  exact: le_trans (lee_tofin hh)
    (exterior_diameter_endpoint_upper (extended_exterior_diameter_specification m S) hsa hsb).
Qed.

(** Source for [projection_exterior_cost_bound]: direct last
    inequality zeta(p(S)) <= zeta(S) in
    the proof of 2.10.34, p. 197.
    Infinite costs and every natural degree
    retain the same positive finite normaliser. *)
Theorem projection_exterior_cost_bound (R : realType) (n k m : nat)
    (p : {linear R_n R n -> R_n R k}) (S : set (R_n R n)) :
  O_star p -> (exterior_diameter_cost m (p @` S)<=exterior_diameter_cost m S)%E.
Proof.
move=> hp; rewrite /exterior_diameter_cost; apply: lee_wpmul2l.
- rewrite lee_fin; exact: ltW (hausdorff_normalisation_positive R m).
- exact: projection_extended_exterior_diameter_bound hp.
Qed.
