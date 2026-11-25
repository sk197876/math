(** Federer (1969), 4.1.11, p. 365: the affine maps in
    the join identity are smooth. Reuse the affine decomposition
    of 2.7.16, pp. 133–134, the finite-dimensional linear bound
    and the continuous polynomial calculus of 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom AffineMaps RealNormUP NormDifferentialUP
  NormFiniteLinearBound NormRegularity NormRegularityOperations InnerNorm
  HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_affine_map_smooth]: every original
    affine map between finite-dimensional Euclidean spaces is
    smooth on each open source, supporting the affine identity
    in Federer 4.1.11, p. 365. The original affine predicate
    of 2.7.16 is retained, including zero-dimensional spaces. *)
Theorem euclidean_affine_map_smooth (R:realType) m n
    (U:set (R_n R m))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) U x)
    (A:R_n R m->R_n R n):
  is_affine_map A->norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U A.
Proof.
move=>hA.
pose L:=@HomMap R (R_n R m) (R_n R n) (affine_linear_part A)
  (introT (asboolP _) (@affine_linear_part_linear R (R_n R m) (R_n R n) A hA)).
have hL:=@norm_finite_linear_bounded R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  m (@coordinate_basis R m) (@coordinate_basisP R m) L.
move=>k.
have hLinear:=@norm_class_linear R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U L k hU hL.
have hConstant:=@norm_class_constant R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U (A 0) k hU.
apply:(norm_class_domain_agreement _ (norm_class_add hConstant hLinear)).
move=>x _;change (A 0+affine_linear_part A x=A x).
exact:esym (affine_decomposition A x).
Qed.

(** Source for [euclidean_affine_segment_values]: affine maps
    preserve the original coefficients 1-t and t, the algebraic
    identity behind A composed with F in Federer 4.1.11, p. 365.
    This is exactly the preceding defining affine law. *)
Lemma euclidean_affine_segment_values (R:realType) m n
    (A:R_n R m->R_n R n):
  is_affine_map A->forall x y t,A ((1-t)*:x+t*:y)=(1-t)*:A x+t*:A y.
Proof. move=>hA x y t;apply:hA;by rewrite subrK. Qed.
