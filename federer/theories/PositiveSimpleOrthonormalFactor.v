(** Federer (1969), 1.8.4, p. 40: choosing orthonormal
    factors with the positive orientation of a nonzero simple vector.
    This refines the orthonormal factorisation of 1.7.5, p. 32,
    by absorbing a scalar of absolute value one into the first factor.
    Positive degree is necessary to have that first factor. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleOrthonormalFactor
  InnerProductUP OrthonormalFamilies ExteriorNorm ExteriorProductFactors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_family_unit_rescaling]: Federer 1.8.4,
    p. 40, supporting preservation of orthonormality under independent
    real scalars of absolute value one, in particular a sign change
    in one factor. *)
Lemma orthonormal_family_unit_rescaling (R : realFieldType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    (I : finType) (e : I -> V) (he : orthonormal_family B e)
    (a : I -> R) (ha : forall i, `|a i|= 1) :
  orthonormal_family B (fun i => a i *: e i).
Proof.
move=> i j; rewrite (bilZl (inner_bilinear hB)) (bilZr (inner_bilinear hB)) he.
change (a i * (a j * (if i == j then 1 else 0)) = (if i == j then 1 else 0)).
case hij : (i == j); last by rewrite !mulr0.
move/eqP: hij=> ->; rewrite mulr1 -expr2.
apply/eqP; by rewrite sqr_norm_eq1 ha eqxx.
Qed.

(** Source for [simple_positive_orthonormal_factor]: Federer 1.8.4,
    p. 40, supporting positive factorisation xi=|xi| times a
    positively oriented orthonormal product. No finite ambient
    dimension is imposed. *)
Theorem simple_positive_orthonormal_factor (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p (hp : (0 < p)%N) (x : exterior_power V p) (hx : x != 0) (hs : simple x) :
  exists e : 'I_p -> V, orthonormal_family B e /\
    x = exterior_norm h2 hB x *: e_lambda e (ord_tuple p).
Proof.
have [e [c [ho [hc hxe]]]] := simple_orthonormal_factor h2 hB hx hs.
have hcn : `|c| != 0 by rewrite normr_eq0.
have hN : exterior_norm h2 hB x = `|c|.
  by rewrite hxe exterior_norm_scale (orthonormal_product_unit_norm h2 hB ho) mulr1.
pose s := c / `|c|.
have hcu : `|c| \is a GRing.unit by rewrite unitfE.
have hsN : `|s|= 1 by rewrite /s normrM (normrV hcu) normr_id mulfV.
pose j : 'I_p := Ordinal hp.
pose a (i : 'I_p) := if i == j then s else 1.
have ha i : `|a i|= 1 by rewrite /a; case: ifP=> _ //; rewrite normr1.
exists (fun i => a i *: e i); split.
- exact (@orthonormal_family_unit_rescaling R V B hB (Finite.clone 'I_p _) e ho a ha).
- rewrite exterior_product_scaled_family.
  have hprod : \prod_i a i = s.
    rewrite (bigD1 j) // /a eqxx.
    have hz : \prod_(i | i != j) (if i == j then s else 1) = 1.
      apply: big1 => i hij; by rewrite (negbTE hij).
    rewrite hz; change (s * 1 = s); by rewrite mulr1.
  rewrite hprod hN scalerA /s mulrCA mulfV // mulr1.
  exact hxe.
Qed.
