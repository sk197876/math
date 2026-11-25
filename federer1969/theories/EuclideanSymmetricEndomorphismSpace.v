(** Federer (1969), 3.2.28(1), printed p. 263: the actual
    codomain Y_m of symmetric linear endomorphisms. Its
    membership is specified by the adjoint law f*=f; the
    subspace carrier and inclusion are the existing abstract interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP
  AdjointUP AdjointCriteria SymmetricEndomorphisms EuclideanRectangularAdjoint
  LinearBasis HomCompositionDeterminant FiniteSubspaceBasisExistence
  EuclideanGramDifferentialAlgebra EuclideanGramTangentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_symmetric_hom_subspace]: Y_m, the
    vector space of symmetric endomorphisms, Federer 3.2.28(1),
    p. 263. The predicate f*=f is equivalent to the
    defining symmetric pairing by 1.7.4, p. 30. *)
Definition euclidean_symmetric_hom_subspace (R:realType) m:
    subspace (Hom (R_n R m) (R_n R m)).
Proof.
apply:(@Subspace R (Hom (R_n R m) (R_n R m))
  (fun f=>euclidean_rectangular_adjoint f=f)).
- exact:linear0.
- move=>f g hf hg; rewrite linearD.
  change (euclidean_rectangular_adjoint f+euclidean_rectangular_adjoint g=f+g).
  by rewrite hf hg.
- move=>c f hf; rewrite linearZ.
  change (c*:euclidean_rectangular_adjoint f=c*:f).
  by rewrite hf.
Defined.
Arguments euclidean_symmetric_hom_subspace {R m}.

(** Source for [euclidean_symmetric_hom_membership]: equivalence
    of the adjoint and symmetric-pairing definitions of Y_m,
    1.7.4, p. 30, used in Federer 3.2.28(1), p. 263. *)
Lemma euclidean_symmetric_hom_membership (R:realType) m
    (f:Hom (R_n R m) (R_n R m)):
  euclidean_symmetric_hom_subspace f <->
  is_symmetric_endomorphism (@euclidean_inner_product R m) (hom_as_linear f).
Proof.
have h:=symmetric_iff_adjoint_equal (@euclidean_inner_productP R m)
  (euclidean_rectangular_adjoint_pairing f).
split.
- move=>he; change (euclidean_rectangular_adjoint f=f) in he; apply:h.2=>x.
  exact:(congr1 (fun g:Hom (R_n R m) (R_n R m)=>g x) he).
- move=>hf; apply:hom_ext; exact:h.1 hf.
Qed.

(** Source for [euclidean_symmetric_hom_finite_basis]: finite
    dimensionality of the actual Y_m, Federer 3.2.28(1),
    p. 263. The exact dimension is a separate obligation;
    this existence theorem assumes no dimension formula. *)
Theorem euclidean_symmetric_hom_finite_basis (R:realType) m:
  exists q (e:'I_q->subspace_space (@euclidean_symmetric_hom_subspace R m)),
    is_basis e /\ (q<=m * m)%N.
Proof.
have [q [e [he hq]]]:=finite_subspace_basis_exists
  (@hom_rank_one_baseP R (R_n R m) (R_n R m) m m
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R m) (@coordinate_basisP R m))
  (@euclidean_symmetric_hom_subspace R m).
exists q,e; split=>//; by rewrite card_prod !card_ord in hq.
Qed.

(** Source for [euclidean_gram_symmetric_range]: P(g) belongs
    to Y_m, Federer 3.2.28(1), p. 263. *)
Lemma euclidean_gram_symmetric_range (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  euclidean_symmetric_hom_subspace (euclidean_gram_map g).
Proof.
apply:(euclidean_symmetric_hom_membership (euclidean_gram_map g)).2.
exact:euclidean_gram_map_symmetric.
Qed.

(** Source for [euclidean_gram_differential_symmetric_range]:
    DP(g) takes values in Y_m, Federer 3.2.28(1), p. 263. *)
Lemma euclidean_gram_differential_symmetric_range (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  euclidean_symmetric_hom_subspace (euclidean_gram_differential g h).
Proof.
apply:(euclidean_symmetric_hom_membership (euclidean_gram_differential g h)).2.
exact:euclidean_gram_differential_symmetric.
Qed.
