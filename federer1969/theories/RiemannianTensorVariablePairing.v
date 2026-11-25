(** Federer (1969), 3.2.46, pp. 281–282: the
    continuous tensor can be evaluated on varying continuous
    coordinate vectors. This supporting step proves the
    continuity needed for the actual Gram Jacobian integrand,
    using 1.7.1 and finite coordinate expansion. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanCoordinateTopology InnerProductUP InnerProductLaws OrthonormalFamilies
  InnerMetric RealMetricBackground RiemannianTensorUP RiemannianTensorSpeedContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [euclidean_inner_form_coordinate_expansion]:
    the actual bilinear form evaluated through the ordinary
    coordinate basis, supporting 3.2.46, pp. 281–282,
    from linearity and the coordinates of 1.7.1, p. 28.
    No matrix or new inner product is selected. *)
Lemma euclidean_inner_form_coordinate_expansion (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B) (v w : R_n R n) :
  B v w=\sum_(i < n) \sum_(j < n)
    v i*w j*B (@coordinate_basis R n i) (@coordinate_basis R n j).
Proof.
have hLeft : B v w=\sum_(i < n) v i*B (@coordinate_basis R n i) w.
  rewrite -(inner_coordinateE hB) -{1}(euclidean_coordinate_expansion v) linear_sum.
  apply: eq_bigr=> i _; by rewrite linearZ inner_coordinateE.
have hRight i : B (@coordinate_basis R n i) w=
    \sum_(j < n) w j*B (@coordinate_basis R n i) (@coordinate_basis R n j).
  rewrite (inner_symmetric hB) -(inner_coordinateE hB)
    -{1}(euclidean_coordinate_expansion w) linear_sum.
  apply: eq_bigr=> j _; by rewrite linearZ inner_coordinateE (inner_symmetric hB).
rewrite hLeft; apply: eq_bigr=> i _; rewrite hRight big_distrr /=.
apply: eq_bigr=> j _; by rewrite mulrA.
Qed.

(** Source for [riemannian_variable_pairing_continuous]:
    x maps to g(p(x))(v(x),w(x)) continuously whenever
    p,v,w are continuous and p takes values in the original
    chart. Supporting the actual Jacobian measurability in
    3.2.46, p. 282; no derivative or frame field is assumed. *)
Lemma riemannian_variable_pairing_continuous (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (X : topologicalType)
    (p v w : X -> inner_metric_space (@euclidean_inner_productP R n))
    (hA : forall x, A (p x)) :
  continuous p -> continuous v -> continuous w ->
  continuous (fun x=>(g (p x) (v x) (w x) : real_line_metric R)).
Proof.
move=> hp hv hw.
have hCoordV i : continuous (fun x=>(v x i : real_line_metric R)).
  move=> x; exact (continuous_comp (hv x) (@euclidean_coordinate_continuous R n i (v x))).
have hCoordW i : continuous (fun x=>(w x i : real_line_metric R)).
  move=> x; exact (continuous_comp (hw x) (@euclidean_coordinate_continuous R n i (w x))).
have hCoefficient i j := @riemannian_coefficient_along_continuous_map R n A g hg X p
  (@coordinate_basis R n i) (@coordinate_basis R n j) hp hA.
have hFormula : (fun x=>(g (p x) (v x) (w x) : real_line_metric R)) =
    (fun x=>(\sum_(i < n) \sum_(j < n) v x i*w x j*
      g (p x) (@coordinate_basis R n i) (@coordinate_basis R n j) : real_line_metric R)).
  apply: funext=> x; exact (@euclidean_inner_form_coordinate_expansion R n (g (p x))
    (riemannian_tensor_inner hg (hA x)) (v x) (w x)).
rewrite hFormula; apply: continuous_big; first exact: add_continuous.
move=> i _; apply: continuous_big; first exact: add_continuous.
move=> j _ x; apply: (@continuousM R X); last exact: hCoefficient i j x.
apply: (@continuousM R X); [exact: hCoordV i x | exact: hCoordW j x].
Qed.
