(** Federer (1969), 4.1.19, p. 377: the
    functional beta on the original Omega pair
    is alpha after q. This supporting adapter
    accepts the independently specified flat-valued q;
    its actual opaque value is supplied by 4.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces FlatCurrentUnionSpace FlatCochainSpace
  CurrentLonePairImageUP CurrentLonePairImageSealed CurrentLonePairFlatUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section PairFunctional.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation E := (@flat_cochain_evaluation R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation raw := (@CurrentLonePair.map R h2 n m U hU).
Variable Q : Hom P W.

(** Source for [flat_cochain_pair_functional]: the
    exact induced beta of Federer 4.1.19,
    p. 377, from an original flat-valued
    q with the defining laws of 4.1.18. *)
Definition flat_cochain_pair_functional (alpha : A) : Hom P R^o :=
  hom_comp (E alpha) Q.

(** Source for [flat_cochain_pair_functional_evaluation]:
    beta(xi,eta)=alpha(q(xi,eta)), Federer 4.1.19,
    p. 377, on the literal original
    compactly supported L1 factors. *)
Lemma flat_cochain_pair_functional_evaluation (alpha : A) (v : P) :
  flat_cochain_pair_functional alpha v = E alpha (Q v).
Proof. exact: hom_compE. Qed.

(** Source for [flat_cochain_pair_functional_zero]:
    the zero original cochain induces the zero
    pair functional, supporting the representation in
    Federer 4.1.19, p. 377. *)
Lemma flat_cochain_pair_functional_zero :
  flat_cochain_pair_functional (0:A) = 0.
Proof.
apply: hom_ext=> v.
by rewrite flat_cochain_pair_functional_evaluation linear0 hom_zeroE.
Qed.

(** Source for [flat_cochain_pair_functional_equal_images]:
    beta depends only on the actual current
    q(xi,eta), Federer 4.1.19, p. 377.
    The independent inclusion law and injectivity
    of the original flat-union carrier suffice. *)
Theorem flat_cochain_pair_functional_equal_images
    (hQ : @is_current_lone_pair_flat_map R h2 n m U hU Q)
    (alpha : A) (v w : P) :
  raw v = raw w ->
  flat_cochain_pair_functional alpha v = flat_cochain_pair_functional alpha w.
Proof.
move=> hEqual.
have hFlat : Q v = Q w.
  apply: (@flat_current_union_inclusion_injective R h2 n m U hU).
  rewrite (hQ v) (hQ w); exact: hEqual.
by rewrite !flat_cochain_pair_functional_evaluation hFlat.
Qed.

(** Source for [flat_cochain_pair_functional_kernel]:
    the induced beta annihilates the actual
    kernel of q, as used in Federer
    4.1.19, p. 377. This direction
    uses no converse kernel-closure assertion. *)
Theorem flat_cochain_pair_functional_kernel
    (hQ : @is_current_lone_pair_flat_map R h2 n m U hU Q)
    (alpha : A) (v : P) :
  raw v = 0 -> flat_cochain_pair_functional alpha v = 0.
Proof.
move=> hZero.
have hImage : raw v = raw (0:P) by rewrite linear0.
have h := @flat_cochain_pair_functional_equal_images hQ alpha v (0:P) hImage.
by rewrite linear0 in h.
Qed.
End PairFunctional.
