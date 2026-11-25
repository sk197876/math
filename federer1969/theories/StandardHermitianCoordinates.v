(** Federer (1969), 1.8.2, p. 39: the real part of the standard Hermitian
    product corresponds to the usual dot product on R^(2 nu) under the
    canonical real-coordinate isomorphism. Coordinates are ordered in two
    blocks, as in ComplexOrderedBases.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarUP ComplexScalarSealed
  ComplexScalarLaws ComplexCoefficientAlgebra FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct HermitianRealImaginary StandardHermitian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation re := (@ComplexScalars.re R).
Local Notation im := (@ComplexScalars.im R).
Variable n : nat.
Local Notation E := (coordinate_space C n).
Local Notation ER := (restricted_space embed E).
Local Notation F := (R_n R (n+n)).

(** Source for [complex_real_coordinates]: Federer 1.8.2,
    p. 39, canonical identification C^nu -> R^(2 nu), listing
    first real coordinates and then imaginary coordinates. *)
Definition complex_real_coordinates (v : ER) : F :=
  [ffun j => match split j with inl i => re (v i) | inr i => im (v i) end].

(** Source for [complex_from_real_coordinates]: Federer 1.8.2,
    p. 39, inverse coordinate identification by a+ib. *)
Definition complex_from_real_coordinates (v : F) : ER :=
  [ffun i => embed (v (lshift n i)) + ii * embed (v (rshift n i))].

(** Source for [complex_real_coordinatesK]: Federer 1.8.2,
    p. 39, recovering a complex vector from its real coordinates. *)
Lemma complex_real_coordinatesK : cancel complex_real_coordinates complex_from_real_coordinates.
Proof.
move=> v; apply/ffunP=> i; rewrite /complex_from_real_coordinates /complex_real_coordinates
  !ffunE (unsplitK (inl _ i)) (unsplitK (inr _ i)).
exact: esym (complex_decomposition (ComplexScalars.laws R) (v i)).
Qed.

(** Source for [complex_from_real_coordinatesK]: Federer 1.8.2,
    p. 39, recovering both real coordinate blocks. *)
Lemma complex_from_real_coordinatesK : cancel complex_from_real_coordinates complex_real_coordinates.
Proof.
move=> v; apply/ffunP=> j; rewrite /complex_real_coordinates ffunE.
case: (split_ordP j) => i ->; rewrite /complex_from_real_coordinates !ffunE.
- by rewrite (complex_re_add (ComplexScalars.laws R)) re_embed re_i_real addr0.
- by rewrite (complex_im_add (ComplexScalars.laws R)) im_embed im_i_real add0r.
Qed.

(** Source for [complex_real_coordinates_linear]: Federer 1.8.2,
    p. 39, the canonical identification is real linear. *)
Lemma complex_real_coordinates_linear : linear complex_real_coordinates.
Proof.
move=> a v w; apply/ffunP=> j; rewrite /complex_real_coordinates !ffunE.
case: (split j) => i; rewrite !ffunE.
- change (re (embed a*v i+w i) = a*re (v i)+re (w i)).
  by rewrite (complex_re_add (ComplexScalars.laws R)) (complex_re_scale (ComplexScalars.laws R)).
- change (im (embed a*v i+w i) = a*im (v i)+im (w i)).
  by rewrite (complex_im_add (ComplexScalars.laws R)) (complex_im_scale (ComplexScalars.laws R)).
Qed.
HB.instance Definition _ := GRing.isLinear.Build R ER F *:%R
  complex_real_coordinates complex_real_coordinates_linear.

(** Source for [standard_hermitian_real_coordinates]: Federer 1.8.2,
    p. 39, the real part of the standard Hermitian product is
    the standard real dot product after the canonical identification. *)
Theorem standard_hermitian_real_coordinates v w :
  hermitian_real_part (@standard_hermitian_product R n) v w =
    euclidean_inner_product (complex_real_coordinates v) (complex_real_coordinates w).
Proof.
have hd : euclidean_inner_product (complex_real_coordinates v) (complex_real_coordinates w) =
    (\sum_i re (v i)*re (w i)) + \sum_i im (v i)*im (w i).
  rewrite /euclidean_inner_product big_split_ord; congr (_+_);
    apply: eq_bigr => i _; by rewrite /complex_real_coordinates !ffunE ?(unsplitK (inl _ i)) ?(unsplitK (inr _ i)).
rewrite hd -big_split.
change (complex_real_part (\sum_i
  (conjugate (v i)*w i : restricted_space embed C^o)) =
  \sum_i (re (v i)*re (w i)+im (v i)*im (w i))).
rewrite linear_sum; apply: eq_bigr => i _.
change (re (conjugate (v i)*w i) = re (v i)*re (w i)+im (v i)*im (w i)).
by rewrite re_mul re_conjugate im_conjugate mulNr opprK.
Qed.
End Coordinates.
