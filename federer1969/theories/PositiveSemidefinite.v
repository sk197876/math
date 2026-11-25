(** Federer (1969), 1.7.3, p. 29: supporting scalar-algebra step in the
    principal-axis argument. The nonnegative form lambda B-S at a maximising
    unit vector has that vector in its radical. Here bilinearity and
    positivity suffice. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_positive_semidefinite]: Federer 1.7.3,
    p. 29, supporting predicate for the maximality argument: the
    diagonal values of a symmetric bilinear form are nonnegative. *)
Record is_positive_semidefinite (R : realFieldType) (V : lmodType R)
    (S : V -> V -> R) : Prop := {
  semidefinite_bilinear : @bilinear R V V R^o S;
  semidefinite_symmetric : forall x y, S x y = S y x;
  semidefinite_nonnegative : forall x, 0 <= S x x
}.

(** Source for [semidefinite_zero_diagonal]: Federer 1.7.3,
    p. 29, supporting stationary-point argument: if S is positive
    semidefinite and S(x,x)=0, then S(x,y)=0 for every y. This is
    a local algebraic proof of the implication used for lambda B-S. *)
Theorem semidefinite_zero_diagonal (R : realFieldType) (V : lmodType R)
    (S : V -> V -> R) (hS : is_positive_semidefinite S) x y :
    S x x = 0 -> S x y = 0.
Proof.
move=> hxx; have [hxy|hxy] := eqVneq (S x y) 0; first exact: hxy.
pose c := (S y y + 1) / (S x y + S x y).
have hb : S x y + S x y != 0.
  by rewrite -mulr2n -mulr_natl mulf_eq0 pnatr_eq0 /= hxy.
have hvx : S (y-c*:x) x = S x y.
  by rewrite (bilBl (semidefinite_bilinear hS)) (bilZl (semidefinite_bilinear hS))
    hxx scaler0 subr0 (semidefinite_symmetric hS).
have hv : S (y-c*:x) (y-c*:x) = -1.
  rewrite (bilBr (semidefinite_bilinear hS)) (bilZr (semidefinite_bilinear hS)) hvx.
  rewrite (bilBl (semidefinite_bilinear hS)) (bilZl (semidefinite_bilinear hS)).
  change (S y y - c * S x y - c * S x y = -1).
  by rewrite -addrA -opprD -mulrDr /c divfK // opprD addrA subrr add0r.
have hh := semidefinite_nonnegative hS (y-c*:x).
by rewrite hv oppr_ge0 ler10 in hh.
Qed.
