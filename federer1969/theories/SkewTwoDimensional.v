(** Federer (1969), 1.7.3, p. 29: the alternating-form normal form in
    dimension two, orienting the basis to make its coefficient nonnegative. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP SymmetricEndomorphisms
  OrthonormalFamilies OrthonormalPairCoordinates GramSchmidt
  OrthonormalisationUP LinearBasis Bilinear BilinearNegation SkewPairUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [skew_two_dimensional_pair]: Federer 1.7.3,
    p. 29, supporting explicit two-dimensional normal form:
    choose an orthonormal pair spanning the space, with nonnegative
    coefficient in the skew map's two-by-two block. *)
Theorem skew_two_dimensional_pair (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : {linear V -> V}) (hf : is_skewsymmetric_endomorphism B f)
    (b : 'I_2 -> V) (hb : is_basis b) :
  exists x y lambda, is_skew_pair B f x y lambda /\
    forall v : V, exists a c : R, v = a *: x+c *: y.
Proof.
have [e [he hgs]] := @orthonormal_basis_exists R V B hB 2 b hb.
have ho := orthonormalisation_orthonormal hgs.
pose x := e ord0; pose y := e ord_max.
pose lambda := B (f x) y.
have hx : B x x = 1 by rewrite /x ho eqxx.
have hy : B y y = 1 by rewrite /y ho eqxx.
have hxy : B x y = 0 by rewrite /x /y ho.
have hfx : f x = lambda *: y.
  have h := @orthonormal_pair_coordinates R V B hB e he ho (f x).
  by rewrite (@skewsymmetric_diagonal_zero R V B hB f hf) scale0r add0r in h.
have hfy : f y = (-lambda) *: x.
  have h := @orthonormal_pair_coordinates R V B hB e he ho (f y).
  rewrite (@skewsymmetric_diagonal_zero R V B hB f hf) scale0r addr0 in h.
  by rewrite hf (inner_symmetric hB y (f x)) in h.
have hs v : v = B v x *: x+B v y *: y.
  exact: (@orthonormal_pair_coordinates R V B hB e he ho v).
have [hl|hl] := lerP 0 lambda.
- exists x, y, lambda; split; first by constructor.
  move=> v; exists (B v x), (B v y); exact: hs.
- exists x, (-y), (-lambda); split.
  + constructor.
    * by rewrite oppr_ge0; exact: ltW hl.
    * exact hx.
    * by rewrite (bilNl (inner_bilinear hB)) (bilNr (inner_bilinear hB)) opprK.
    * by rewrite (bilNr (inner_bilinear hB)) hxy oppr0.
    * by rewrite hfx scaleNr scalerN opprK.
    * by rewrite linearN hfy opprK scaleNr opprK.
  + move=> v; exists (B v x), (-B v y).
    by rewrite scaleNr scalerN opprK; exact: hs.
Qed.
