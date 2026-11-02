(** Private existence proofs for the gradient of Federer (1969),
    3.1.1, p. 209. Finite dimension uses the polarity of 1.7.2; the
    complete-space case uses the sealed representation of 1.7.13.
    Downstream modules must use DifferentialGradientSealed instead. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  topology num_normedtype normed_module.
From Federer Require Import Hom InnerProductUP InnerProductLaws InnerNorm
  InnerMetric InnerNormedTopology OrthonormalFamilies OrthonormalisationUP
  GramSchmidt LinearBasis HilbertSpaceUP HilbertFunctionalUP HilbertFunctional
  RealMetricBackground NormMetricScaleContinuity NormDifferentialUP DifferentialGradientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [finite_differential_gradient_exists]: the finite-dimensional
    gradient assertion in Federer 3.1.1, p. 209, using the polarity
    isomorphism of 1.7.2, pp. 28–29. Coordinates provide a private witness;
    the exposed specification remains the intrinsic pairing equation. *)
Lemma finite_differential_gradient_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (L : Hom V R^o) :
  exists u, is_differential_gradient B L u.
Proof.
have [d [hd ho]] := orthonormal_basis_exists hB he.
have hdo := orthonormalisation_orthonormal ho.
pose u := \sum_i L (d i) *: d i.
exists u=> v.
have heq : hom_as_linear L v = inner_coordinate hB u v.
  apply: (basis_linear_ext hd (hom_as_linear L) (inner_coordinate hB u))=> j.
  rewrite hom_as_linearE inner_coordinateE (inner_symmetric hB).
  rewrite -(@inner_coordinateE R V B hB (d j) u).
  exact: esym (@orthonormal_coefficient R V B hB _ d hdo (fun i => L (d i)) j).
by rewrite hom_as_linearE inner_coordinateE in heq.
Qed.

(** Source for [hilbert_differential_gradient_exists]: Federer 3.1.1,
    p. 209, complete inner-product case. The bounded differential is a
    continuous real functional, so 1.7.13, p. 37, supplies its vector
    through the existing sealed representation equation. *)
Lemma hilbert_differential_gradient_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hH : is_hilbert_space hB) (L : Hom V R^o) :
  norm_bounded_linear (inner_norm hB) (fun t => `|t|) L ->
  exists u, is_differential_gradient B L u.
Proof.
move=> [C [hC hL]].
have hc : continuous (fun x : inner_metric_space hB =>
    (hom_as_linear L x : R^o)).
  apply: (@metric_fixed_lipschitz_continuous R (inner_metric_space hB)
    (real_line_metric R) _ C hC).
  move=> x y; change (`|L x-L y| <= C*inner_norm hB (x-y)).
  by rewrite -linearB; exact: hL.
exists (@hilbert_functional_vector R V B hB hH (hom_as_linear L) hc)=> v.
rewrite (inner_symmetric hB).
exact: (@hilbert_functional_vectorP R V B hB hH (hom_as_linear L) hc v).
Qed.

(** Source for [differential_gradient_exists]: both alternatives of
    the gradient existence statement in Federer 3.1.1, p. 209. *)
Theorem differential_gradient_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hspace : differential_gradient_space hB) (L : Hom V R^o) :
  norm_bounded_linear (inner_norm hB) (fun t => `|t|) L ->
  exists u, is_differential_gradient B L u.
Proof.
move=> hL; case: hspace=> [[n [e he]]|hH].
- exact: (@finite_differential_gradient_exists R V B hB n e he L).
- exact: (@hilbert_differential_gradient_exists R V B hB hH L hL).
Qed.
