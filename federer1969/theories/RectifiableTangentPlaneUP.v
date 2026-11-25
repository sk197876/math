(** Federer (1969), 3.2.19, p. 256: intrinsic meaning of
    the approximate tangent being an m-dimensional vector subspace.
    No plane is chosen globally or postulated to exist. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_m_dimensional_approximate_tangent]: the vector-space
    assertion in Federer 3.2.19, p. 256. Equality with a member
    of G(R^n,m) specifies both vector-subspace laws and the actual basis
    dimension of the approximate tangent cone, rather than merely containment
    in some plane. *)
Definition is_m_dimensional_approximate_tangent (R : realType) n m
    (mu : set (R_n R n) -> \bar R) w : Prop :=
  exists P : GrassmannSubspaces.G (R_n R n) m,
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
      mu m w=[set v | grassmann_val P v].
