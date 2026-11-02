(** Federer (1969), 3.1.1, p. 211, and 3.1.15, p. 227:
    the linear map h |-> sum_i h_i v_i on R^m determined by
    prescribed values v_i on the standard basis, with the bound
    ||sum_i h_i v_i||<=|h| sum_i |e_i| ||v_i|| from Cauchy's
    inequality; it assembles D D^k f from the approximate partial
    derivatives of the coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormInequalities HilbertFormCompactness RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CoordinateHom.
Variable R : realType.
Variable m : nat.
Local Notation X := (R_n R m).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.

(** Source for [coordinate_hom_fun]:
    the map h |-> sum_i h_i v_i, Federer 3.1.1, p. 211,
    "Df(a)(h)=sum_i h_i D_i f(a)". *)
Definition coordinate_hom_fun (v : 'I_m->Y) (h : X) : Y := \sum_i h i*:v i.

(** Source for [coordinate_hom_linear]:
    linearity of the coordinate combination, Federer 3.1.1, p. 211. *)
Lemma coordinate_hom_linear (v : 'I_m->Y) : linear (coordinate_hom_fun v).
Proof.
move=>c x y; rewrite /coordinate_hom_fun scaler_sumr -big_split /=.
by apply: eq_bigr=>i _; rewrite !ffunE scalerDl scalerA.
Qed.

(** Source for [coordinate_hom]:
    the linear map of 3.1.1, p. 211, as an element of Hom. *)
Definition coordinate_hom (v : 'I_m->Y) : Hom X Y :=
  @HomMap R X Y (coordinate_hom_fun v) (introT (asboolP _) (coordinate_hom_linear v)).

(** Source for [coordinate_homE]:
    evaluation of the coordinate combination. *)
Lemma coordinate_homE (v : 'I_m->Y) (h : X) : coordinate_hom v h=\sum_i h i*:v i.
Proof. by []. Qed.

(** Source for [euclidean_coordinate_inner]:
    the coordinate h_i is the inner product of h with the ith
    standard vector, Federer 1.7.1, p. 28. *)
Lemma euclidean_coordinate_inner (h : X) (i : 'I_m) :
  euclidean_inner_product h (@coordinate_basis R m i)=h i.
Proof.
rewrite /euclidean_inner_product (bigD1 i) //= big1 ?addr0.
- by rewrite ffunE eqxx mulr1.
- by move=>j hj; rewrite ffunE (negbTE hj) mulr0.
Qed.

(** Source for [euclidean_coordinate_bound]:
    |h_i|<=|h| |e_i| by Cauchy's inequality, Federer 1.7.1, p. 28. *)
Lemma euclidean_coordinate_bound (h : X) (i : 'I_m) :
  `|h i|<=N h*N (@coordinate_basis R m i).
Proof. rewrite -euclidean_coordinate_inner; exact: inner_cauchy. Qed.

(** Source for [coordinate_hom_bound]:
    ||sum_i h_i v_i||<=|h| sum_i |e_i| ||v_i||, the finite linear
    bound used for D D^k f in Federer 3.1.15, p. 227. *)
Lemma coordinate_hom_bound (v : 'I_m->Y) (h : X) :
  NY (coordinate_hom v h)<=N h*\sum_i N (@coordinate_basis R m i)*NY (v i).
Proof.
rewrite coordinate_homE mulr_sumr.
apply: (le_trans (real_seminorm_sum hNY.1 _)); apply: ler_sum=>i _.
rewrite (real_seminorm_scale hNY.1) mulrA.
apply: ler_wpM2r; first exact: (real_seminorm_nonnegative hNY.1).
exact: euclidean_coordinate_bound.
Qed.

(** Source for [coordinate_hom_bounded]:
    the coordinate combination is a bounded linear map,
    Federer 3.1.1, p. 209. *)
Lemma coordinate_hom_bounded (v : 'I_m->Y) : norm_bounded_linear N NY (coordinate_hom v).
Proof.
exists (\sum_i N (@coordinate_basis R m i)*NY (v i)); split.
- apply: sumr_ge0=>i _; apply: mulr_ge0; [exact: (real_seminorm_nonnegative hN.1)|
    exact: (real_seminorm_nonnegative hNY.1)].
- move=>h; rewrite mulrC; exact: coordinate_hom_bound.
Qed.

(** Source for [coordinate_hom_difference_bound]:
    the difference of two coordinate combinations is bounded by
    the differences of the values, supporting the continuity of
    D D^k f on the Lusin set in Federer 3.1.15, p. 227. *)
Lemma coordinate_hom_difference_bound (v w : 'I_m->Y) (h : X) :
  NY ((coordinate_hom v-coordinate_hom w) h)<=
    N h*\sum_i N (@coordinate_basis R m i)*NY (v i-w i).
Proof.
have -> : (coordinate_hom v-coordinate_hom w) h=coordinate_hom (fun i=>v i-w i) h.
  rewrite -[-coordinate_hom w]scaleN1r hom_addE hom_scaleE !coordinate_homE scaleN1r -sumrB.
  by apply: eq_bigr=>i _; rewrite scalerBr.
exact: coordinate_hom_bound.
Qed.
End CoordinateHom.
