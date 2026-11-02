(** Federer (1969), 3.2.28(1), printed p. 263: the Gram map
    P(g)= g* g, its differential and its orthogonal level set.
    Adjoint maps are used only through their sealed pairing laws.
    Operator norms give equivalent finite-dimensional calculus norms;
    the Hausdorff geometry will use the inner product of 1.7.9. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerProductUP InnerNorm
  InnerProductLaws AdjointUP AdjointLaws AdjointCriteria OrthogonalMaps
  SymmetricEndomorphisms EuclideanRectangularAdjoint EuclideanHomOperator
  HomSpaceTopology CoareaAdjointBound NormBoundedBilinearUP
  NormBilinearDifferentialAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_composition_operator_bound]: supporting the
    polynomial differential in Federer 3.2.28(1), p. 263; the
    composition estimate is 1.7.6, p. 33, in finite Euclidean spaces. *)
Lemma euclidean_composition_operator_bound (R:realType) a b c
    (f:Hom (R_n R b) (R_n R c)) (g:Hom (R_n R a) (R_n R b)):
  euclidean_operator_norm (hom_comp f g)<=
    euclidean_operator_norm f * euclidean_operator_norm g.
Proof.
apply:hom_operator_norm_least.
- by rewrite mulr_ge0 ?hom_operator_norm_nonnegative.
move=>x; rewrite hom_compE.
apply:le_trans (@hom_operator_norm_bound R (R_n R b) (R_n R c)
  (@euclidean_inner_product R b) (@euclidean_inner_product R c)
  (@euclidean_inner_productP R b) (@euclidean_inner_productP R c)
  b (@coordinate_basis R b) (@coordinate_basisP R b) f (g x)) _.
rewrite -mulrA; apply:ler_wpM2l; first exact:hom_operator_norm_nonnegative.
exact:hom_operator_norm_bound.
Qed.

(** Source for [euclidean_adjoint_operator_bound]: supporting the
    continuity of the Gram polynomial in Federer 3.2.28(1), p. 263;
    the adjoint norm equality is 1.7.6, p. 33. *)
Lemma euclidean_adjoint_operator_bound (R:realType) m n
    (f:Hom (R_n R m) (R_n R n)):
  euclidean_operator_norm (euclidean_rectangular_adjoint f)<=
    euclidean_operator_norm f.
Proof.
apply:hom_operator_norm_least; first exact:hom_operator_norm_nonnegative.
apply:euclidean_rectangular_adjoint_bound; first exact:hom_operator_norm_nonnegative.
exact:hom_operator_norm_bound.
Qed.

(** Source for [euclidean_gram_pair_bilinear]: the bilinear expression
    g* h underlying P in Federer 3.2.28(1), p. 263. *)
Lemma euclidean_gram_pair_bilinear (R:realType) m n:
  bilinear (fun (g h:Hom (R_n R m) (R_n R n))=>
    hom_comp (euclidean_rectangular_adjoint g) h).
Proof.
split.
- move=>h c g f; rewrite euclidean_rectangular_adjoint_linear.
  exact:hom_precompose_linear.
- move=>g; exact:hom_postcompose_linear.
Qed.

(** Source for [euclidean_gram_pair_bounded]: supporting smoothness
    of P, Federer 3.2.28(1), p. 263. The bound is proved for the
    actual bilinear operation, including zero-dimensional spaces. *)
Lemma euclidean_gram_pair_bounded (R:realType) m n:
  norm_bounded_bilinear (@euclidean_operator_norm R m n)
    (@euclidean_operator_norm R m n) (@euclidean_operator_norm R m m)
    (fun g h=>hom_comp (euclidean_rectangular_adjoint g) h).
Proof.
split; first exact:euclidean_gram_pair_bilinear.
exists 1; split; first exact:ler01.
move=>g h; rewrite mul1r.
apply:le_trans (euclidean_composition_operator_bound _ _) _.
apply:ler_wpM2r; first exact:hom_operator_norm_nonnegative.
exact:euclidean_adjoint_operator_bound.
Qed.

(** Source for [euclidean_gram_map]: P(g)= g* g in Federer
    3.2.28(1), p. 263. This is an expression in already specified
    composition and sealed adjoint operations, not a chosen witness. *)
Definition euclidean_gram_map (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):=
  hom_comp (euclidean_rectangular_adjoint g) g.

(** Source for [euclidean_gram_differential]: DP(g)h= h* g+g* h,
    Federer 3.2.28(1), p. 263. The first-order term is linear
    by the previously proved bilinear differential algebra. *)
Definition euclidean_gram_differential (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):=
  norm_bilinear_product_linear_term (@euclidean_gram_pair_bilinear R m n)
    g g (hom_of_linear (linear_id _)) (hom_of_linear (linear_id _)).

(** Source for [euclidean_gram_differentialE]: the displayed
    differential formula, Federer 3.2.28(1), p. 263. *)
Lemma euclidean_gram_differentialE (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  euclidean_gram_differential g h=
    hom_comp (euclidean_rectangular_adjoint h) g+
    hom_comp (euclidean_rectangular_adjoint g) h.
Proof. by []. Qed.

(** Source for [euclidean_gram_map_symmetric]: P takes values in
    the symmetric endomorphism space Y_m, Federer 3.2.28(1), p. 263. *)
Lemma euclidean_gram_map_symmetric (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_symmetric_endomorphism (@euclidean_inner_product R m)
    (hom_as_linear (euclidean_gram_map g)).
Proof.
exact:(@adjoint_source_square_symmetric R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (hom_as_linear g) (hom_as_linear (euclidean_rectangular_adjoint g))
  (euclidean_rectangular_adjoint_pairing g)).
Qed.

(** Source for [euclidean_gram_differential_symmetric]: the
    differential takes values in Y_m as well, Federer 3.2.28(1),
    p. 263; supporting expansion of the displayed formula. *)
Lemma euclidean_gram_differential_symmetric (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  is_symmetric_endomorphism (@euclidean_inner_product R m)
    (hom_as_linear (euclidean_gram_differential g h)).
Proof.
move=>x y; rewrite euclidean_gram_differentialE.
change (euclidean_inner_product
  (euclidean_rectangular_adjoint h (g x)+euclidean_rectangular_adjoint g (h x)) y=
  euclidean_inner_product x
  (euclidean_rectangular_adjoint h (g y)+euclidean_rectangular_adjoint g (h y))).
rewrite (bilDl (inner_bilinear (@euclidean_inner_productP R m)))
  (bilDr (inner_bilinear (@euclidean_inner_productP R m))).
rewrite (inner_symmetric (@euclidean_inner_productP R m)
  (euclidean_rectangular_adjoint h (g x)) y)
  (inner_symmetric (@euclidean_inner_productP R m)
  (euclidean_rectangular_adjoint g (h x)) y)
  !euclidean_rectangular_adjoint_pairing.
rewrite (inner_symmetric (@euclidean_inner_productP R n) (h y) (g x))
  (inner_symmetric (@euclidean_inner_productP R n) (g y) (h x)).
exact:addrC.
Qed.

(** Source for [euclidean_gram_orthogonal_level]: the exact
    identity O(n,m)= P^{-1}{identity}, Federer 3.2.28(1), p. 263. *)
Lemma euclidean_gram_orthogonal_level (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) <->
  euclidean_gram_map g= hom_of_linear (linear_id _).
Proof.
have h:=orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R m)
  (euclidean_rectangular_adjoint_pairing g).
split.
- move=>hg; apply:hom_ext=>x; exact:(h.1 hg).
- move=>he.
  have hCan:cancel g (euclidean_rectangular_adjoint g).
    move=>x; have hx:=congr1 (fun f:Hom (R_n R m) (R_n R m)=>f x) he.
    exact hx.
  exact:(h.2 hCan).
Qed.
