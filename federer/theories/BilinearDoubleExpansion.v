(** Federer (1969), 1.7.5, pp. 32-33: the double expansion of a wedge
    product in two exterior bases. Supporting generic bilinear algebra, with
    possibly distinct input spaces. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [bilinear_double_expansion]: Federer 1.7.5,
    pp. 32-33, bilinearity expands the product of two sums
    as the double sum of products of coefficients times products
    of basis vectors. *)
Lemma bilinear_double_expansion (R : fieldType) (V W Z : lmodType R)
    (b : V -> W -> Z) (hb : bilinear b) (I J : finType)
    (e : I -> V) (f : J -> W) (c : I -> R) (d : J -> R) :
  b (\sum_i c i *: e i) (\sum_j d j *: f j) =
    \sum_i \sum_j (c i * d j) *: b (e i) (f j).
Proof.
rewrite (big_morph (fun x => b x (\sum_j d j *: f j))
  (fun x y => bilDl hb x y _) (bil0l hb _)).
apply: eq_bigr => i _; rewrite (bilZl hb).
rewrite (big_morph (fun y => b (e i) y) (bilDr hb (e i)) (bil0r hb (e i))).
rewrite scaler_sumr; apply: eq_bigr => j _; by rewrite (bilZr hb) scalerA.
Qed.
