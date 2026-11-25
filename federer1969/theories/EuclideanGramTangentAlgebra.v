(** Federer (1969), 3.2.28(1)–(2), printed pp. 263–264:
    surjectivity of DP, its kernel equation and the horizontal
    splitting used for the oriented Grassmann map. This file
    proves the algebra; geometric tangent identifications follow
    from the regular-level and tangent theorems of 3.1.19–3.1.21. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm
  AdjointUP AdjointLaws AdjointCriteria OrthogonalMaps
  SymmetricEndomorphisms EuclideanRectangularAdjoint
  EuclideanGramDifferentialAlgebra LinearRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_gram_differential_pairing]: the
    bilinear expansion of DP(g), Federer 3.2.28(1), p. 263,
    supporting its symmetric range and kernel equations. *)
Lemma euclidean_gram_differential_pairing (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)) x y:
  euclidean_inner_product x (euclidean_gram_differential g h y)=
    euclidean_inner_product (h x) (g y)+
    euclidean_inner_product (g x) (h y).
Proof.
rewrite euclidean_gram_differentialE hom_addE
  (bilDr (inner_bilinear (@euclidean_inner_productP R m))).
by rewrite !hom_compE !euclidean_rectangular_adjoint_pairing.
Qed.

(** Source for [euclidean_gram_differential_surjective]: if g
    is injective, im DP(g)= Y_m, Federer 3.2.28(1), p. 263.
    The factor t with t g= s is taken from the proved linear
    retraction laws only inside this existence proof. *)
Theorem euclidean_gram_differential_surjective (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  injective g -> forall s:Hom (R_n R m) (R_n R m),
    is_symmetric_endomorphism (@euclidean_inner_product R m) (hom_as_linear s) ->
    exists h:Hom (R_n R m) (R_n R n), euclidean_gram_differential g h= s.
Proof.
move=>hg s hs.
pose r:=hom_of_linear (@linear_retraction R (R_n R m) (R_n R n)
  (hom_as_linear g) hg).
have hr x:r (g x)= x:=linear_retractionK hg x.
pose t:=hom_comp s r.
pose h:=(2:R)^-1*:euclidean_rectangular_adjoint t.
exists h; apply:hom_ext=>y.
apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>x.
rewrite euclidean_gram_differential_pairing /h hom_scaleE.
rewrite (bilZl (inner_bilinear (@euclidean_inner_productP R n)))
  (bilZr (inner_bilinear (@euclidean_inner_productP R n)))
  (inner_symmetric (@euclidean_inner_productP R n)
    (euclidean_rectangular_adjoint t x) (g y))
  !euclidean_rectangular_adjoint_pairing /t !hom_compE !hr.
rewrite (inner_symmetric (@euclidean_inner_productP R m) (s y) x) hs.
by rewrite -mulrDl -mulr2n -(mulr_natr ((2:R)^-1) 2) mulVf ?pnatr_eq0 // mul1r.
Qed.

(** Source for [euclidean_gram_kernel_skew]: the kernel
    equation h* g+g* h= 0 is equivalent to g* h being
    skewsymmetric, Federer 3.2.28(2), p. 264. *)
Theorem euclidean_gram_kernel_skew (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  euclidean_gram_differential g h= 0 <->
  is_skewsymmetric_endomorphism (@euclidean_inner_product R m)
    (hom_as_linear (hom_comp (euclidean_rectangular_adjoint g) h)).
Proof.
split.
- move=>hz x y.
  have hp:=euclidean_gram_differential_pairing g h x y.
  rewrite hz hom_zeroE (bil0r (inner_bilinear (@euclidean_inner_productP R m))) in hp.
  change (euclidean_inner_product (euclidean_rectangular_adjoint g (h x)) y=
    -euclidean_inner_product x (euclidean_rectangular_adjoint g (h y))).
  rewrite (inner_symmetric (@euclidean_inner_productP R m))
    !euclidean_rectangular_adjoint_pairing
    (inner_symmetric (@euclidean_inner_productP R n) (g y) (h x)).
  apply/eqP; rewrite -addr_eq0; apply/eqP; exact:esym hp.
- move=>hs; apply:hom_ext=>y.
  apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>x.
  rewrite hom_zeroE (bil0r (inner_bilinear (@euclidean_inner_productP R m)))
    euclidean_gram_differential_pairing.
  have hp:=hs x y.
  change (euclidean_inner_product (euclidean_rectangular_adjoint g (h x)) y=
    -euclidean_inner_product x (euclidean_rectangular_adjoint g (h y))) in hp.
  rewrite (inner_symmetric (@euclidean_inner_productP R m))
    !euclidean_rectangular_adjoint_pairing
    (inner_symmetric (@euclidean_inner_productP R n) (g y) (h x)) in hp.
  by rewrite hp addNr.
Qed.
