(** Federer (1969), 1.7.5, pp. 32-33: the norm induced by the inner product
    on each exterior power. The same abstract norm laws as in 1.7.1 are
    used, without a coordinate definition. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerExterior InnerExteriorPositivity
  InnerExteriorBasis ExteriorGrading FiniteExteriorPowers ExteriorDeterminant
  OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Norm.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [exterior_norm]: Federer 1.7.5, p. 32,
    the norm of an m-vector is the nonnegative square root of
    its induced inner product with itself. *)
Definition exterior_norm m := inner_norm (@exterior_inner_productP R h2 V B hB m).

(** Source for [exterior_norm_square]: Federer 1.7.5,
    p. 32, the square of the induced norm equals xi dot xi. *)
Lemma exterior_norm_square m (x : exterior_power V m) :
  exterior_norm x ^+ 2 = exterior_inner_form h2 hB x x.
Proof. exact: inner_norm_sqr. Qed.

(** Source for [exterior_norm_nonnegative]: Federer 1.7.5,
    p. 32, supporting nonnegativity of the induced norm. *)
Lemma exterior_norm_nonnegative m (x : exterior_power V m) : 0 <= exterior_norm x.
Proof. exact: inner_norm_nonnegative. Qed.

(** Source for [exterior_norm_zero]: Federer 1.7.5,
    p. 32, the zero multivector has norm zero, in every degree. *)
Lemma exterior_norm_zero m : exterior_norm (0 : exterior_power V m) = 0.
Proof. exact: inner_norm0. Qed.

(** Source for [exterior_norm_eq0]: Federer 1.7.5,
    p. 32, positive definiteness: norm zero means vector zero. *)
Lemma exterior_norm_eq0 m (x : exterior_power V m) :
  (exterior_norm x == 0) = (x == 0).
Proof. exact: inner_norm_eq0. Qed.

(** Source for [exterior_norm_scale]: Federer 1.7.5,
    p. 32, supporting absolute homogeneity of the induced norm. *)
Lemma exterior_norm_scale m (x : exterior_power V m) c :
  exterior_norm (c *: x) = `|c| * exterior_norm x.
Proof. exact: inner_normZ. Qed.

(** Source for [orthonormal_product_unit_norm]: Federer
    1.7.5, p. 32, an exterior product of orthonormal vectors
    has norm one, including the empty product. *)
Lemma orthonormal_product_unit_norm m (e : 'I_m -> V)
    (he : orthonormal_family B e) :
  exterior_norm (e_lambda e (ord_tuple m)) = 1.
Proof.
apply: inner_norm_value; first exact: ler01.
have hh := @exterior_orthonormal_family R h2 V B hB m e he m
  (Lambda_top m) (Lambda_top m).
rewrite eqxx in hh.
rewrite expr1n; symmetry; exact hh.
Qed.
End Norm.
