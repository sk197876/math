(** Federer (1969), 3.4.12, p. 339:
    original complex submanifolds are specified by local
    holomorphic straightening to actual complex vector planes.
    The definition assumes no real dimension conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ModuleQuotient ScalarRestriction ComplexScalarSealed RealNormUP
  NormDifferentialUP GrassmannSubspaces HolomorphicDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_submanifold]: the original
    definition of a complex m-dimensional holomorphic submanifold
    in 3.4.12, p. 339. The original
    maps, neighbourhood and complex plane are existence witnesses. *)
Definition is_holomorphic_submanifold (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x))
    m (S:set X):=
  forall b,S b ->exists (T C:set X) (s t:X->X) (Z:G X m),
    @norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX T b /\
    is_holomorphic_diffeomorphism hNX T C s t /\
    s @` (S `&` T)=[set x|grassmann_val Z x /\C x].
