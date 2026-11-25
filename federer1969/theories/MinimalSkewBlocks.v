(** Federer (1969), 1.7.3, pp. 29-30: the minimal invariant pieces
    contributing to an alternating two-form. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  InnerProductUP InnerProductRestriction SymmetricEndomorphisms InvariantRestriction
  MinimalInvariantUP MinimalSymmetricDimension MinimalSkewDimension
  AnnihilatorDimension SkewPairUP SkewOneDimensional SkewTwoDimensional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [minimal_skew_block_alternative]: Federer
    1.7.3, pp. 29-30, each minimal invariant piece either
    contributes zero or is spanned by an oriented orthonormal pair
    carrying one nonnegative skew block. *)
Theorem minimal_skew_block_alternative (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (f : {linear V -> V}) (hf : is_skewsymmetric_endomorphism B f)
    (W : subspace V) (hW : is_minimal_invariant_subspace f W) :
  (forall x, W x -> f x = 0) \/
  (exists x y lambda, W x /\ W y /\ is_skew_pair B f x y lambda /\
    forall v, W v -> exists a c : R, v = a *: x+c *: y).
Proof.
have [k [a [ha hk]]] := @finite_subspace_basis_exists R V n b hb W.
have hd := @minimal_skewsymmetric_dimension R V B hB f hf W hW k a ha.
have hn := @minimal_invariant_positive_dimension R V f W hW k a ha.
have hcases : forall j, (0 < j)%N -> (j <= 2)%N -> j = 1%N \/ j = 2%N.
  by move=> [|[|[|j]]] //; [left | right].
have hsize := hcases k hn hd.
pose C := @restricted_inner_product R V B W.
have hC := @restricted_inner_productP R V B hB W.
pose g := @invariant_restriction R V f W (minimal_invariant_stable hW).
have hg : is_skewsymmetric_endomorphism C g.
  exact: skewsymmetric_invariant_restriction hf.
case: hsize => hsize; subst k.
- left=> x hx.
  have hz := @skew_one_dimensional_zero R (subspace_space W) C hC g hg a ha
    (subspace_lift hx).
  have h := congr1 (@subspace_val R V W) hz.
  by rewrite linear0 in h.
- right.
  have [x [y [lambda [hp hs]]]] := @skew_two_dimensional_pair R
    (subspace_space W) C hC g hg a ha.
  exists (subspace_val x), (subspace_val y), lambda; split; first exact: subspace_valP.
  split; first exact: subspace_valP.
  split.
  + constructor.
    * exact: skew_pair_nonnegative hp.
    * exact: skew_pair_first_unit hp.
    * exact: skew_pair_second_unit hp.
    * exact: skew_pair_orthogonal hp.
    * have h := congr1 (@subspace_val R V W) (skew_pair_first_image hp).
      by rewrite linearZ in h.
    * have h := congr1 (@subspace_val R V W) (skew_pair_second_image hp).
      by rewrite linearZ in h.
  + move=> v hv; have [r [s he]] := hs (subspace_lift hv).
    exists r, s; have h := congr1 (@subspace_val R V W) he.
    by rewrite linearD !linearZ in h.
Qed.
