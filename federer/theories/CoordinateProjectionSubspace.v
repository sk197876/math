(** Federer (1969), 1.7.4, p. 31, penultimate paragraph: some coordinate
    projection is injective on every m-dimensional subspace W of R^n. The
    proof uses a nonzero Grassmann coordinate of the product of a basis of
    W, as in the book's exterior-power argument. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  GrassmannAbbreviations FiniteCoordinates ExteriorIndices FiniteExteriorPowers
  CoordinateProjection CoordinateProjectionVolume IndependentMap
  InnerProductUP InnerPolarity EuclideanInnerProduct
  SubspaceBasisProduct AssociatedInitialCoordinates GrassmannCoordinates
  CovectorProducts CovectorSimpleProducts SimpleWordIndependence
  AlternatingCoordinates AlternatingPairing Bilinear TensorUP
  FiniteIndependence FiniteDimension FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SubspaceProjection.
Variable R : realFieldType.
Variables n m : nat.
Variable W : subspace (R_n R n).
Variable e : 'I_m -> subspace_space W.
Hypothesis he : is_basis e.

(** Source for [coordinate_projection_independent_images]:
    Federer 1.7.4, p. 31, penultimate paragraph: a nonzero
    selected top covector yields independent projected basis images. *)
Theorem coordinate_projection_independent_images :
  exists lambda : Lambda n m,
    finite_independent (fun i => coordinate_projection lambda (subspace_val (e i))).
Proof.
have h2 : (1+1 : R) != 0 by change (2%:R != (0:R)); rewrite pnatr_eq0.
pose omega := @euclidean_coordinate_covector R n.
have hdual i j : omega i [tuple @coordinate_basis R n j] = if i==j then 1 else 0.
  by rewrite /omega euclidean_coordinate_covectorE /coordinate_basis ffunE eq_sym.
pose xi := @subspace_basis_product R (R_n R n) W m e.
have hxi := @subspace_basis_product_nonzero R h2 (R_n R n) W m e he.
have [lambda hl] := @nonzero_Grassmann_coordinate R h2 (R_n R n) n m
  (@coordinate_basis R n) omega (@coordinate_basisP R n) hdual xi hxi.
exists lambda.
apply: nonzero_word_independent; apply: product_word_nonzero.
apply/eqP=> hz; move: hl.
rewrite /xi_lambda /xi /subspace_basis_product /omega coordinate_projection_volume_pairing
  hz (bil0l (@pairing_bilinear R (R_n R m) R^o m)) eqxx.
by [].
Qed.

(** Source for [coordinate_projection_subspace_isomorphism]:
    Federer 1.7.4, p. 31, p_lambda composed with the inclusion
    of W is an isomorphism. The witness includes a two-sided
    linear inverse, including when m is zero. *)
Theorem coordinate_projection_subspace_isomorphism :
  exists (lambda : Lambda n m) (q : {linear R_n R m -> subspace_space W}),
    cancel (fun x => coordinate_projection lambda (subspace_val x)) q /\
    cancel q (fun x => coordinate_projection lambda (subspace_val x)).
Proof.
have [lambda hl] := coordinate_projection_independent_images.
pose f := linear_comp
  (GRing.Linear.clone _ _ _ _ (coordinate_projection lambda) _) (subspace_inclusion W).
have hb : is_basis (fun i => f (e i)).
  apply: (@finite_independent_basis R (finite_basis_vect (@coordinate_basisP R m))
    m (fun i => f (e i))); last exact hl.
  by rewrite finite_basis_dimension card_ord.
have [q [h1 h2]] := basis_image_inverse_exists he hb.
by exists lambda, q; split.
Qed.

(** Source for [coordinate_projection_separates_subspace]:
    Federer 1.7.4, p. 31, final display of the penultimate
    paragraph: W intersect ker p_lambda is the zero subspace. *)
Theorem coordinate_projection_separates_subspace :
  exists lambda : Lambda n m, forall x,
    W x -> coordinate_projection lambda x = 0 -> x = 0.
Proof.
have [lambda [q [h1 h2]]] := coordinate_projection_subspace_isomorphism.
exists lambda => x hx hz.
have hh := h1 (subspace_lift hx).
rewrite subspace_liftE hz linear0 in hh.
have h := congr1 (@subspace_val R (R_n R n) W) hh.
by rewrite linear0 subspace_liftE in h; exact: esym h.
Qed.
End SubspaceProjection.
