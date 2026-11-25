(** Federer (1969), 4.1.12, p. 369: a
    filling in the second factor gives a product
    filling and the original boundary correction in
    the first factor. Reuse every actual degree and
    sign in the preceding 4.1.8 boundary formulas. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianBoundaryPositiveAligned CurrentCartesianBoundarySecondZero
  CurrentBoundary CurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianFillingBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA d := (@current_space R h2 m A hA d).
Local Notation CB d := (@current_space R h2 n B hB d).
Local Notation P i j := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB).
Local Notation bdA d := (@current_boundary R h2 m d A hA).
Local Notation bdB d := (@current_boundary R h2 n d B hB).
Local Notation bdC d := (@current_boundary R h2 (m+n) d AB hAB).
Local Notation Tr a b e := (@current_degree_transport R h2 (m+n) AB hAB a b e).

(** Source for [current_cartesian_filling_boundary_positive]:
    S times boundary B equals the signed product
    filling boundary minus the signed first-factor
    boundary product. This is the algebraic use of
    4.1.8, p. 360, in the first flat product
    estimate of Federer 4.1.12, p. 369. *)
Theorem current_cartesian_filling_boundary_positive i j (S:CA i.+1) (B0:CB j.+1):
  P i.+1 j S (bdB j B0)=
    (-(-1:R)^+i.+1)*:Tr _ _ (eq_trans (addnS i j) (esym (addSn i j)))
      (P i j.+1 (bdA i S) B0)+
    bdC (i.+1+j) ((-1:R)^+i.+1*:Tr _ _ (addnS i.+1 j) (P i.+1 j.+1 S B0)).
Proof.
rewrite (linZ (hom_linear (bdC (i.+1+j))))
  (@current_cartesian_boundary_positive_aligned R h2 m n A B hA hB i j S B0)
  scalerDr scalerA -expr2 sqrr_sign scale1r scaleNr addrA addNr add0r.
by [].
Qed.

(** Source for [current_cartesian_filling_boundary_zero]:
    when S has degree zero, S times boundary B
    is simply the product filling boundary. This
    retains the zero-degree endpoint of the first
    flat product estimate in Federer 4.1.12,
    p. 369, by 4.1.8, p. 360. *)
Theorem current_cartesian_filling_boundary_zero j (S:CA 0%N) (B0:CB j.+1):
  P 0%N j S (bdB j B0)=
    bdC (0+j) (Tr _ _ (addnS 0%N j) (P 0%N j.+1 S B0)).
Proof. exact:esym (@current_cartesian_boundary_second_zero R h2 m n A B hA hB j S B0). Qed.
End CurrentCartesianFillingBoundary.
