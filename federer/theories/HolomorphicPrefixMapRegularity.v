(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),
    p. 326: the original complex prefix projection and inclusion
    are holomorphic. Use finite complex linear holomorphy, the
    original source basis and the standard Hermitian coordinate norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates
  LinearBasis HolomorphicUP FiniteComplexLinearHolomorphic HolomorphicCoordinateNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_prefix_projection_holomorphic]: each original
    complex coordinate projection is holomorphic on its whole
    original source, extending 3.4.8(1), p. 326. *)
Theorem holomorphic_prefix_projection_holomorphic (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    n (e:'I_n->X) (he:is_basis e) j (P:Hom X (coordinate_space (ComplexScalars.C R) j)):
  is_holomorphic hNX (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) setT P.
Proof.
exact:(@finite_complex_linear_holomorphic R X (coordinate_space (ComplexScalars.C R) j)
  NX (@holomorphic_coordinate_norm R j) hNX (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) n e he P).
Qed.

(** Source for [holomorphic_prefix_inclusion_holomorphic]: each original
    complex coordinate inclusion is holomorphic on its whole
    coordinate space, extending 3.4.8(1),(5), pp. 326, 328. *)
Theorem holomorphic_prefix_inclusion_holomorphic (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    j (S:Hom (coordinate_space (ComplexScalars.C R) j) X):
  is_holomorphic (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) hNX setT S.
Proof.
exact:(@finite_complex_linear_holomorphic R (coordinate_space (ComplexScalars.C R) j) X
  (@holomorphic_coordinate_norm R j) NX (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) hNX
  j (@coordinate_basis (ComplexScalars.C R) j) (@coordinate_basisP (ComplexScalars.C R) j) S).
Qed.
