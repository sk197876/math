(** Federer (1969), 1.7.6, p. 33: operator norms agree under the polarity
    and gamma identifications. This supporting transport lemma states only
    the norm-preserving and surjectivity properties used in those arguments. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [operator_norm_isometric_transport]: Federer
    1.7.6, p. 33, supporting invariance under isometric
    identifications. A surjective norm-preserving source map and
    agreement of image lengths identify the two unit-ball suprema. *)
Theorem operator_norm_isometric_transport (R : rcfType)
    (V U X Y : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (D : X -> X -> R) (E : Y -> Y -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (hD : is_inner_product D) (hE : is_inner_product E)
    (f : {linear V -> U}) (g : {linear X -> Y})
    (s : V -> X) (hs : forall x, inner_norm hD (s x) = inner_norm hB x)
    (hsur : forall z, exists x, s x = z)
    (hv : forall x, inner_norm hE (g (s x)) = inner_norm hC (f x)) L M :
  is_operator_norm hB hC f L -> is_operator_norm hD hE g M -> L = M.
Proof.
move=> hL hM; apply/eqP; rewrite eq_le; apply/andP; split.
- have [x [hx <-]] := operator_norm_attained hL.
  rewrite -(hv x).
  apply: (@operator_norm_unit_bound R X Y D E hD hE g M hM).
  by rewrite hs.
- have [z [hz <-]] := operator_norm_attained hM.
  have [x hx] := hsur z; rewrite -hx hv.
  apply: (@operator_norm_unit_bound R V U B C hB hC f L hL).
  by rewrite -(hs x) hx.
Qed.
