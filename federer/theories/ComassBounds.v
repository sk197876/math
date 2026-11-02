(** Federer (1969), 1.8.1, p. 38: consequences of the comass supremum
    definition. All results use the abstract supremum laws, without a
    construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  InnerExteriorPositivity ExteriorNorm ExteriorGrading AlternatingCoordinates
  AlternatingPairing AlternatingForms SimpleElementary AssociatedSubspace
  SimpleUnitBall ComassUP ExteriorPairingBound ExteriorCovectorInner LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Local Notation S := (@simple_unit_ball R h2 V B hB m).
Local Notation N := (@exterior_norm R h2 V B hB m).
Local Notation P := (@pairing_bilinear R V R^o m).

(** Source for [comass_absolute_unit_bound]: Federer 1.8.1, p. 38,
    supporting absolute pairing bound on S, obtained from its symmetry. *)
Lemma comass_absolute_unit_bound phi c (hc : is_comass h2 hB phi c) x :
  S x -> `|pairing x phi| <= c.
Proof.
move=> hx; rewrite ler_norml; apply/andP; split.
- have hh := comass_upper_law hc (simple_unit_ball_opp hm hx).
  rewrite -scaleN1r (bilZl P) scaleN1r in hh.
  by rewrite lerNl.
- exact (@comass_upper_law R h2 V B hB m phi c hc x hx).
Qed.

(** Source for [comass_simple_bound]: Federer 1.8.1, p. 38,
    supporting homogeneous version: evaluation on any simple vector is
    bounded in absolute value by its Euclidean norm times the comass. *)
Theorem comass_simple_bound phi c (hc : is_comass h2 hB phi c) x :
  simple x -> `|pairing x phi| <= N x * c.
Proof.
move=> hs; have [->|hx] := eqVneq x 0.
- by rewrite (bil0l P) normr0 exterior_norm_zero mul0r.
pose y := inner_normalize (@exterior_inner_productP R h2 V B hB m) x.
have hy : S y.
  split; first exact: simple_scale hm hs.
  rewrite /exterior_norm; by rewrite inner_normalize_norm.
have hb := comass_absolute_unit_bound hc hy.
have hh := ler_wpM2l (exterior_norm_nonnegative h2 hB x) hb.
rewrite -(ger0_norm (exterior_norm_nonnegative h2 hB x)) -normrM in hh.
have hk : N x * pairing y phi = pairing x phi.
  change ((N x *: pairing y phi : R^o) = pairing x phi).
  rewrite -(bilZl P).
  by rewrite /y inner_normalizeK.
by rewrite hk (ger0_norm (exterior_norm_nonnegative h2 hB x)) in hh.
Qed.

(** Source for [comass_zero]: Federer 1.8.1, p. 38,
    supporting norm law: the zero covector has comass zero. *)
Lemma comass_zero : is_comass h2 hB (0 : A_m V R^o m) 0.
Proof.
constructor.
- move=> x hx; by rewrite (bil0r P).
- move=> eps heps; exists 0; split; first exact: simple_unit_ball_zero.
  by rewrite (bil0r P) sub0r oppr_lt0.
Qed.

(** Source for [comass_definite]: Federer 1.8.1, p. 38,
    supporting definiteness of the claimed norm: vanishing comass
    forces the alternating form to vanish on every tuple. *)
Theorem comass_definite (phi : A_m V R^o m) : is_comass h2 hB phi 0 -> phi = 0.
Proof.
move=> hc; apply: form_ext => t.
have hs : simple (e_lambda (@idfun V) t) by exists t.
have hh := comass_simple_bound hc hs.
rewrite mulr0 normr_le0 in hh.
have hz : pairing (e_lambda (@idfun V) t) phi = 0 := eqP hh.
by rewrite pairing_tuple in hz; rewrite hz form_zeroE.
Qed.

(** Source for [comass_triangle]: Federer 1.8.1, p. 38,
    supporting triangle inequality for the norm defined by the supremum. *)
Theorem comass_triangle (phi psi : A_m V R^o m) c d b :
  is_comass h2 hB phi c -> is_comass h2 hB psi d ->
  is_comass h2 hB (phi+psi) b -> b <= c+d.
Proof.
move=> hc hd hb; apply: (@comass_least_upper_bound R h2 V B hB m (phi+psi) b hb (c+d)) => x hx.
rewrite (bilDr P); exact: lerD (comass_upper_law hc hx) (comass_upper_law hd hx).
Qed.
End Bounds.
