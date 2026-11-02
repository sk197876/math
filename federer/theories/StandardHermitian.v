(** Federer (1969), 1.8.2, p. 39, coordinate example: H(v,w)=sum_j
    conjugate(v_j) w_j on C^nu. The zero-dimensional example is included.
    This explicit construction is checked against the preceding abstract
    Hermitian specification. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP ScalarRestriction ComplexScalarSealed ComplexScalarUP
  ComplexScalarLaws ComplexCoefficientAlgebra FiniteCoordinates HermitianUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Standard.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Variable n : nat.
Local Notation E := (coordinate_space C n).
Local Notation ER := (restricted_space embed E).
Local Notation CR := (restricted_space embed C^o).

(** Source for [standard_hermitian_product]: Federer 1.8.2,
    p. 39, the displayed coordinate Hermitian product on C^nu. *)
Definition standard_hermitian_product (v w : E) : C := \sum_i conjugate (v i) * w i.

(** Source for [standard_hermitian_bilinear]: Federer 1.8.2,
    p. 39, supporting real bilinearity of the coordinate example. *)
Lemma standard_hermitian_bilinear : @bilinear R ER ER CR standard_hermitian_product.
Proof.
split.
- move=> w a v z; rewrite /standard_hermitian_product.
  under eq_bigr do rewrite !ffunE.
  change ((\sum_i conjugate (embed a * v i+z i) * w i) =
    embed a * (\sum_i conjugate (v i)*w i) + \sum_i conjugate (z i)*w i).
  under eq_bigr do rewrite conjugate_add conjugate_scale mulrDl -mulrA.
  by rewrite big_split mulr_sumr.
- move=> v a w z; rewrite /standard_hermitian_product.
  under eq_bigr do rewrite !ffunE.
  change ((\sum_i conjugate (v i) * (embed a * w i+z i)) =
    embed a * (\sum_i conjugate (v i)*w i) + \sum_i conjugate (v i)*z i).
  under eq_bigr do rewrite mulrDr [conjugate _ * (embed _ * _)]mulrCA.
  by rewrite big_split mulr_sumr.
Qed.

(** Source for [standard_hermitian_i_right]: Federer 1.8.2,
    p. 39, supporting i-linearity in the second coordinate slot. *)
Lemma standard_hermitian_i_right v w :
  standard_hermitian_product v (ii *: w) = ii * standard_hermitian_product v w.
Proof.
rewrite /standard_hermitian_product mulr_sumr; apply: eq_bigr => j _.
by rewrite ffunE mulrCA.
Qed.

(** Source for [standard_hermitian_symmetric]: Federer 1.8.2,
    p. 39, supporting conjugate symmetry of the coordinate example. *)
Lemma standard_hermitian_symmetric v w :
  standard_hermitian_product w v = conjugate (standard_hermitian_product v w).
Proof.
have hc0 : @conjugate R 0 = 0 by rewrite -(rmorph0 embed) conjugate_real.
rewrite /standard_hermitian_product (big_morph (@conjugate R) (@conjugate_add R) hc0).
apply: eq_bigr => j _; by rewrite conjugate_mul conjugateK mulrC.
Qed.

(** Source for [standard_hermitian_diagonal]: Federer 1.8.2,
    p. 39, supporting diagonal sum of squared complex absolute values. *)
Lemma standard_hermitian_diagonal v : ComplexScalars.re (standard_hermitian_product v v) =
  \sum_i norm_square (v i).
Proof.
change (complex_real_part (\sum_i (conjugate (v i)*v i : CR)) = \sum_i norm_square (v i)).
rewrite linear_sum; apply: eq_bigr => j _.
change (ComplexScalars.re (conjugate (v j)*v j) = norm_square (v j)).
by rewrite mulrC mul_conjugate re_embed.
Qed.

(** Source for [standard_hermitian_productP]: Federer 1.8.2,
    p. 39, the displayed coordinate construction satisfies all
    Hermitian laws, including positivity and the empty-dimensional case. *)
Theorem standard_hermitian_productP : is_hermitian_product standard_hermitian_product.
Proof.
constructor; [exact: standard_hermitian_bilinear | exact: standard_hermitian_i_right |
  exact: standard_hermitian_symmetric |].
move=> v hv; rewrite standard_hermitian_diagonal lt0r.
apply/andP; split; last by apply: sumr_ge0 => j _; exact: norm_square_ge0.
apply/eqP=> hz; apply: (elimT negP hv); apply/eqP/ffunP=> j; rewrite ffunE.
have hj := psumr_eq0P (fun i _ => norm_square_ge0 (v i)) hz (i:=j) isT.
apply/eqP; by rewrite -norm_square_eq0 hj eqxx.
Qed.
End Standard.
