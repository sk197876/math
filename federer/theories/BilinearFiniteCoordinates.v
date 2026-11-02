(** Federer (1969), 1.7.3, p. 29: supporting coordinate expansion for
    continuity of a bilinear form in finite dimension. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Expansion.
Variable R : fieldType.
Variable V : lmodType R.
Variable S : V -> V -> R.
Hypothesis hS : @bilinear R V V R^o S.
Variable I J : finType.
Variable e : I -> V.
Variable f : J -> V.

(** Source for [bilinear_finite_expansion]: Federer 1.7.3,
    p. 29, supporting expansion of S on finite linear combinations
    as a double sum of products of coordinates and matrix entries. *)
Lemma bilinear_finite_expansion (c : I -> R) (d : J -> R) :
  S (\sum_i c i *: e i) (\sum_j d j *: f j) =
  \sum_i \sum_j (c i * d j) * S (e i) (f j).
Proof.
rewrite (big_morph (fun x => S x (\sum_j d j *: f j))
  (fun x y => bilDl hS x y _) (bil0l hS _)).
apply: eq_bigr => i _; rewrite (bilZl hS).
rewrite (big_morph (fun y => S (e i) y) (bilDr hS (e i)) (bil0r hS (e i))).
rewrite scaler_sumr; apply: eq_bigr => j _; rewrite (bilZr hS).
change (c i * (d j * S (e i) (f j)) = (c i * d j) * S (e i) (f j)).
by rewrite mulrA.
Qed.
End Expansion.
