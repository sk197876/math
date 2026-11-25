(** Federer (1969), 2.7.16, p. 136: "The L^n measure of a rectangular box Q
    = {x : 0 <= (x - a) . e_i <= c_i for i = 1, ..., n}, where a in R^n, c_i
    >= 0, and e_1, ..., e_n form an orthonormal base of R^n, equals the
    product c_1 ... c_n." Federer gives no proof. The box is a + g(P), where
    P = {z : 0 <= z_i <= c_i} and g(z) = sum_i z_i e_i is orthogonal (1.7.2,
    p. 28); hence L^n(Q) = |det g| L^n(P) = c_1 ... c_n by translation
    invariance, the determinant formula of 2.7.16, p. 134, and |det g| = 1
    (1.7.6, p. 33). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerMetric InnerNormedTopology LinearBasis OrthogonalMaps OrthonormalFamilies
  OrthogonalFinite MeasureUP EuclideanLebesgue EuclideanLebesgueDimensions
  EuclideanLebesgueTranslation EuclideanLebesgueBoxes EuclideanLinearMaps EuclideanLebesgueDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectangularBox.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation B := (@euclidean_inner_product R n).

(** Source for [euclidean_rectangular_box]: Federer 2.7.16, p. 136,
    "The L^n measure of a rectangular box
    Q = {x : 0 <= (x - a) . e_i <= c_i for i = 1, ..., n}, where
    a in R^n, c_i >= 0, and e_1, ..., e_n form an orthonormal base of
    R^n, equals the product c_1 ... c_n". Direct formalisation. *)
Theorem euclidean_rectangular_box (a : E) (c : 'I_n -> R) (e : 'I_n -> V) :
  (forall i, 0 <= c i) -> orthonormal_family B e ->
  Leb [set x : E | forall i, 0 <= B (x - a) (e i) <= c i] = (\prod_(i < n) c i)%:E.
Proof.
move=> hc he.
pose g := euclidean_frame_map e.
have hg : is_orthogonal_map B B g := euclidean_frame_orthogonal he.
have hsurj := orthogonal_endomorphism_surjective (@euclidean_inner_productP R n) (@coordinate_basisP R n) hg.
pose P := [set z : E | forall i, 0 <= z i <= c i].
have hQ : [set x : E | forall i, 0 <= B (x - a) (e i) <= c i] = [set a + y | y in (g : E -> E) @` P].
  apply/seteqP; split=> x /=.
  - move=> hx; have [z hz] := hsurj (x - a).
    exists (x - a); last by rewrite addrC subrK.
    exists z=> // i; rewrite /=; have := hx i.
    by rewrite -hz /g /= (euclidean_frame_inner he).
  - move=> [y [z hz <-] <-] i; rewrite addrC addKr /g /= (euclidean_frame_inner he).
    exact: hz i.
rewrite hQ euclidean_lebesgue_translation euclidean_lebesgue_linear_image.
rewrite (euclidean_orthogonal_det hg) mul1e /P.
rewrite (@euclidean_closed_box R n (fun _ => 0) c); last by [].
by congr (_%:E); apply: eq_bigr=> i _; rewrite subr0.
Qed.

End RectangularBox.
