(** Federer (1969), 2.5.15, p. 108: the Daniell integral lambda(f)=f(xi) on
    K(X) is point evaluation. The unit point mass at xi, which is one on the
    sets containing xi and zero otherwise, is a measure of the kind defined
    in 2.1.2, p. 53; it satisfies the level estimate t nu{f>t} <= f(xi) and
    is continuous along sequences of sets, so that the envelope estimates of
    2.5.2, p. 92, show that the K(X) regular measure of lambda dominates it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [point_mass]: the unit point mass at a point, the
    measure behind the Daniell integral f mapped to f(xi) in Federer
    2.5.15, p. 108, by 2.5.2, p. 92. *)
Definition point_mass (R : realType) (X : Type) (x0 : X) (S : set X) : \bar R :=
  if `[< S x0 >] then 1 else 0.

(** Source for [point_mass_in]: value one on sets containing the
    point, Federer 2.5.15, p. 108. *)
Lemma point_mass_in (R : realType) (X : Type) (x0 : X) (S : set X) :
  S x0 -> point_mass R x0 S = 1.
Proof. by move=> h; rewrite /point_mass asboolT. Qed.

(** Source for [point_mass_out]: value zero on sets avoiding the
    point, Federer 2.5.15, p. 108. *)
Lemma point_mass_out (R : realType) (X : Type) (x0 : X) (S : set X) :
  ~ S x0 -> point_mass R x0 S = 0.
Proof. by move=> h; rewrite /point_mass asboolF. Qed.

(** Source for [point_mass_nonnegative]: supporting nonnegativity of
    the point mass, Federer 2.1.2, p. 53. *)
Lemma point_mass_nonnegative (R : realType) (X : Type) (x0 : X) (S : set X) :
  0 <= point_mass R x0 S.
Proof. by rewrite /point_mass; case: ifP=> _ //; rewrite lee_fin ler01. Qed.

(** Source for [point_mass_le1]: supporting bound one for the point
    mass, Federer 2.5.15, p. 108. *)
Lemma point_mass_le1 (R : realType) (X : Type) (x0 : X) (S : set X) :
  point_mass R x0 S <= 1.
Proof. by rewrite /point_mass; case: ifP=> _ //; rewrite lee_fin ler01. Qed.

(** Source for [point_mass_is_measure]: the point mass is a measure
    in the sense of Federer 2.1.2, p. 53: a countable cover of a set
    containing the point has a member containing the point. *)
Theorem point_mass_is_measure (R : realType) (X : choiceType) (x0 : X) :
  is_measure (point_mass R x0).
Proof.
constructor; first by move=> S; exact: point_mass_nonnegative.
move=> A F hF hsub.
case: (pselect (A x0))=> [hA|hA]; last first.
  by rewrite point_mass_out //; exact: nonnegative_sum_nonnegative.
have [B hB hBx] := hsub x0 hA.
rewrite (point_mass_in _ hA) -(point_mass_in R hBx).
exact: nonnegative_sum_term hB.
Qed.

(** Source for [point_mass_level_bound]: the level estimate
    t nu{f>t} <= f(xi) for the point mass and the evaluation functional
    of Federer 2.5.15, p. 108, used with the envelope estimate of
    2.5.2, p. 92. *)
Lemma point_mass_level_bound (R : realType) (X : Type) (x0 : X) (f : X -> R) (t : R) :
  (0 <= f x0)%R -> (0 < t)%R -> t%:E * point_mass R x0 [set x | (t < f x)%R] <= (f x0)%:E.
Proof.
move=> hf ht; case: (pselect (t < f x0)%R)=> hx.
- by rewrite (point_mass_in R (S := [set x | (t < f x)%R]) hx) mule1 lee_fin ltW.
- by rewrite (point_mass_out R (S := [set x | (t < f x)%R]) hx) mule0 lee_fin.
Qed.

(** Source for [point_mass_increasing_union]: continuity of the point
    mass along sequences of sets, Federer 2.5.15, p. 108: a union
    containing the point has a member containing it. *)
Lemma point_mass_increasing_union (R : realType) (X : Type) (x0 : X)
    (V : nat -> set X) (c : \bar R) :
  (forall n, point_mass R x0 (V n) <= c) -> point_mass R x0 (\bigcup_n V n) <= c.
Proof.
move=> hc; case: (pselect ((\bigcup_n V n) x0))=> [[n _ hn]|hn].
- rewrite (point_mass_in R (S := \bigcup_n V n)); last by exists n.
  by rewrite -(point_mass_in R (S := V n) hn); exact: hc.
- rewrite (point_mass_out R (S := \bigcup_n V n) hn).
  exact: le_trans (point_mass_nonnegative R x0 (V 0%N)) (hc 0%N).
Qed.
