(** Federer (1969), 1.8.1, pp. 38-39: supporting reduction of comass upper
    bounds to simple unit vectors. Scaling then handles the whole simple
    unit ball. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNormalization InnerExteriorPositivity
  ExteriorGrading ExteriorNorm AlternatingCoordinates AlternatingPairing
  AssociatedSubspace SimpleElementary ComassUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [comass_simple_sphere_upper_bound]: Federer 1.8.1,
    pp. 38-39, supporting normalization step for comass estimates.
    A nonnegative bound on simple unit vectors bounds the comass;
    no unit vector need exist, so degrees above the dimension are included. *)
Theorem comass_simple_sphere_upper_bound (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    m (hm : (0 < m)%N) (phi : A_m V R^o m) c d :
  is_comass h2 hB phi c -> 0 <= d ->
  (forall x, simple x -> exterior_norm h2 hB x = 1 -> `|pairing x phi| <= d) -> c <= d.
Proof.
move=> hc hd hunit.
apply: (@comass_least_upper_bound R h2 V B hB m phi c hc d) => x [hs hxN].
have [->|hx] := eqVneq x 0; first by rewrite (bil0l (@pairing_bilinear R V R^o m)).
pose y := inner_normalize (@exterior_inner_productP R h2 V B hB m) x.
have hy : simple y := simple_scale _ hm hs.
have hyN : exterior_norm h2 hB y = 1 := inner_normalize_norm _ hx.
have hh := ler_wpM2l (exterior_norm_nonnegative h2 hB x) (hunit y hy hyN).
have hvalue : exterior_norm h2 hB x * pairing y phi = pairing x phi.
  change ((exterior_norm h2 hB x *: pairing y phi : R^o) = pairing x phi).
  rewrite -(bilZl (@pairing_bilinear R V R^o m)).
  by rewrite /y inner_normalizeK.
rewrite -(ger0_norm (exterior_norm_nonnegative h2 hB x)) -normrM hvalue in hh.
rewrite (ger0_norm (exterior_norm_nonnegative h2 hB x)) in hh.
have ht := ler_wpM2r hd hxN; rewrite mul1r in ht.
exact: (le_trans (ler_norm _) (le_trans hh ht)).
Qed.
