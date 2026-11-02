(** Federer (1969), 3.2.28(4), printed pp. 266–267:
    the map T(x)= x^2/2 into the actual second symmetric power,
    its metric formula and its two-point fibres on the unit sphere.
    All norms are those induced by 1.10.5, not the mass norms. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import TensorUP Bilinear BilinearNegation InnerProductUP InnerProductLaws
  InnerNorm InnerUnitEquality SymmetricAlgebra SymmetricGrading
  SymmetricFormIsomorphism InnerSymmetric InnerSymmetricPositivity
  SymmetricInnerNorm SymmetricInnerPurePowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_projective_square]: T(x)= x^2/2, Federer
    3.2.28(4), p. 266. The symmetric power and its product
    are the previously sealed objects of 1.9.1 and 1.10.5. *)
Definition inner_projective_square (R:realType) (V:lmodType R) (x:V):
    symmetric_power V 2:=
  (2:R)^-1*:symmetric_tuple_component [tuple x | i<2].

Section Geometry.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation N:=(inner_norm hB).
Local Notation T:=(@inner_projective_square R V).
Local Notation S:=(@symmetric_inner_form R V B hB 2).
Local Notation hS:=(@symmetric_inner_productP R V B hB 2).
Local Notation NS:=(inner_norm hS).

(** Source for [inner_projective_square_pairing]: the formula
    x^2.y^2= 2(x.y)^2 in Federer 3.2.28(4), p. 267,
    including the factor one half in the definition of T. *)
Lemma inner_projective_square_pairing x y:
  S (T x) (T y)= (B x y)^+2/2.
Proof.
rewrite /inner_projective_square
  (bilZl (inner_bilinear hS)) (bilZr (inner_bilinear hS))
  symmetric_inner_pure_powers /= .
change ((2:R)^-1*((2:R)^-1*(2*(B x y)^+2))= (B x y)^+2/2).
by rewrite [(2:R)^-1*(2*(B x y)^+2)]mulrA mulVf ?pnatr_eq0 // mul1r mulrC.
Qed.

(** Source for [inner_projective_square_distance_general]: the
    displayed squared-distance identity for x^2-y^2,
    Federer 3.2.28(4), p. 267, with the normalization of T. *)
Lemma inner_projective_square_distance_general x y:
  NS (T x-T y)^+2=
    ((N x)^+4+(N y)^+4)/2-(B x y)^+2.
Proof.
rewrite inner_norm_sqr (bilBl (inner_bilinear hS))
  !(bilBr (inner_bilinear hS))
  !inner_projective_square_pairing
  (inner_symmetric hB y x) -!(inner_norm_sqr hB).
have hHalf:(2:R)^-1+(2:R)^-1= 1.
  by rewrite -mulr2n -(mulr_natr ((2:R)^-1) 2) mulVf ?pnatr_eq0.
rewrite -!exprM.
nra.
Qed.

(** Source for [inner_projective_square_antipodal]: T(x)= T(-x),
    supporting the two-point fibres of Federer 3.2.28(4), p. 267. *)
Lemma inner_projective_square_antipodal x:T (-x)= T x.
Proof.
apply/eqP; rewrite -subr_eq0 -(inner_norm_eq0 hS) -sqrf_eq0
  inner_projective_square_distance_general inner_normN
  (bilNl (inner_bilinear hB)) -inner_norm_sqr exprNn /= .
have hHalf:(2:R)^-1+(2:R)^-1= 1.
  by rewrite -mulr2n -(mulr_natr ((2:R)^-1) 2) mulVf ?pnatr_eq0.
apply/eqP; nra.
Qed.

(** Source for [inner_projective_square_unit_distance]: for unit
    x,y, |T(x)-T(y)|^2= 1-(x.y)^2, Federer 3.2.28(4), p. 267. *)
Lemma inner_projective_square_unit_distance x y:
  N x= 1 ->N y= 1 ->NS (T x-T y)^+2= 1-(B x y)^+2.
Proof.
move=>hx hy; rewrite inner_projective_square_distance_general hx hy !expr1n.
change ((2:R)/2-(B x y)^+2= 1-(B x y)^+2).
by rewrite divff ?pnatr_eq0.
Qed.

(** Source for [inner_projective_square_unit_fibre]: for unit
    x,y, T(x)= T(y) iff x= y or x= -y, Federer 3.2.28(4), p. 267.
    Positivity is inherited from the actual symmetric-power metric. *)
Theorem inner_projective_square_unit_fibre x y:
  N x= 1 ->N y= 1 ->(T x= T y <->x= y \/ x= -y).
Proof.
move=>hx hy; split.
- move=>he.
  have hd:=inner_projective_square_unit_distance hx hy.
  rewrite he subrr inner_norm0 expr0n in hd.
  change ((0:R)= 1-(B x y)^+2) in hd.
  have hs:(B x y)^+2= (1:R)^+2.
    rewrite expr1n; symmetry; apply/eqP; rewrite -subr_eq0.
    apply/eqP; exact:esym hd.
  have /orP [/eqP hp|/eqP hp]:(B x y==1)||(B x y== -1).
    by rewrite -eqf_sqr hs eqxx.
  + left; exact:(@inner_unit_pair_equality R V B hB x y hx hy).1 hp.
  + right.
    have hny:N (-y)= 1 by rewrite inner_normN hy.
    apply:(@inner_unit_pair_equality R V B hB x (-y) hx hny).1.
    by rewrite (bilNr (inner_bilinear hB)) hp opprK.
- move=>[->|->]; first reflexivity.
  exact:inner_projective_square_antipodal.
Qed.
End Geometry.
