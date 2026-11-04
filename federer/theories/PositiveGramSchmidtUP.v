(** Federer (1969), 3.2.47, p. 282: the specified local section
    uses Gram–Schmidt with the actual positive residual normalization.
    The earlier prefix-span specification alone permits sign changes;
    the following independent laws retain the printed recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNormalization OrthonormalisationUP
  OrthonormalProjection FinitePrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_gram_schmidt_residual]: the residual
    before division by its length in the recursion of 3.2.47,
    p. 282. This supporting form allows any independent ordered
    finite input; the spherical section will substitute (u,e_2,...,e_n). *)
Definition positive_gram_schmidt_residual (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u v:'I_n->V) (i:'I_n):=
  u i-orthonormal_projection hB (family_prefix (ltnW (ltn_ord i)) v) (u i).

(** Source for [is_positive_gram_schmidt]: independent laws of
    the actual normalized recurrence in 3.2.47, p. 282.
    Positivity is an existence obligation, not a new axiom;
    no parameter-dependent choice of signs is allowed. *)
Record is_positive_gram_schmidt (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u v:'I_n->V):Prop:={
  (** Source for [positive_gram_schmidt_orthonormalisation]:
      orthonormality and every prefix span in the Gram–Schmidt
      recursion of 3.2.47, p. 282, by 1.7.1, p. 28. *)
  positive_gram_schmidt_orthonormalisation:is_orthonormalisation B u v;
  (** Source for [positive_gram_schmidt_nonzero]: each actual
      residual in 3.2.47, p. 282, is nonzero, so its printed
      norm is a strictly positive denominator. *)
  positive_gram_schmidt_nonzero:forall i,positive_gram_schmidt_residual hB u v i!=0;
  (** Source for [positive_gram_schmidt_equation]: the actual
      positive normalization, rather than an unspecified orthonormal
      family, in the recursion of 3.2.47, p. 282. *)
  positive_gram_schmidt_equation:forall i,v i=
    inner_normalize hB (positive_gram_schmidt_residual hB u v i)
}.
