(** Federer (1969), 4.1.8, p. 362: the
    factors in an oriented rectangular parallelepiped.
    Each pair of endpoints has its own Euclidean
    dimension and original containing open set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDirac CurrentBoundary
  CurrentSegmentMapUP OrientedSegmentCurrentSealed OrientedSegmentCurrentBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [oriented_segment_factor]: an original
    pair u_k,v_k in the same Euclidean space,
    with an original containing domain, supporting
    the finite Stokes formula in Federer 4.1.8,
    p. 362. Different factors may have different dimensions. *)
Record oriented_segment_factor (R:realType):={
  (** Source for [oriented_segment_factor_dimension]: the
      Euclidean dimension for the k-th endpoint pair,
      Federer 4.1.8, p. 362. *)
  oriented_segment_factor_dimension:nat;
  (** Source for [oriented_segment_factor_domain]: an
      original open set containing that segment,
      supporting Federer 4.1.8, p. 362. *)
  oriented_segment_factor_domain:set (R_n R oriented_segment_factor_dimension);
  (** Source for [oriented_segment_factor_open]: the
      original openness hypothesis on its test domain,
      Federer 4.1.8, p. 362. *)
  oriented_segment_factor_open:forall x,oriented_segment_factor_domain x->
    norm_domain_interior (inner_norm (@euclidean_inner_productP R oriented_segment_factor_dimension))
      oriented_segment_factor_domain x;
  (** Source for [oriented_segment_factor_start]: the
      original endpoint u_k, Federer 4.1.8, p. 362. *)
  oriented_segment_factor_start:R_n R oriented_segment_factor_dimension;
  (** Source for [oriented_segment_factor_end]: the
      original endpoint v_k, Federer 4.1.8, p. 362. *)
  oriented_segment_factor_end:R_n R oriented_segment_factor_dimension;
  (** Source for [oriented_segment_factor_contains]: the
      original containing-domain condition on the
      k-th closed segment, Federer 4.1.8, p. 362. *)
  oriented_segment_factor_contains:@is_current_segment_domain R oriented_segment_factor_dimension
    oriented_segment_factor_domain oriented_segment_factor_start oriented_segment_factor_end
}.

(** Source for [oriented_segment_factor_current]: the
    original [u_k,v_k], using only the released
    opaque segment laws, supporting the finite product
    in Federer 4.1.8, p. 362. *)
Definition oriented_segment_factor_current (R:realType) (h2:(1+1:R)!=0)
    (a:oriented_segment_factor R):=
  @OrientedSegmentCurrent.value R h2 (oriented_segment_factor_dimension a)
    (@oriented_segment_factor_domain R a) (@oriented_segment_factor_open R a)
    (oriented_segment_factor_start a) (oriented_segment_factor_end a) (@oriented_segment_factor_contains R a).

(** Source for [oriented_segment_factor_endpoint_difference]:
    the original delta_(u_k)-delta_(v_k) appearing
    with sign (-1)^k in the finite Stokes
    display of Federer 4.1.8, p. 362. *)
Definition oriented_segment_factor_endpoint_difference (R:realType) (h2:(1+1:R)!=0)
    (a:oriented_segment_factor R):=
  @dirac_current R h2 (oriented_segment_factor_dimension a)
    (@oriented_segment_factor_domain R a) (@oriented_segment_factor_open R a) (oriented_segment_factor_start a)-
  @dirac_current R h2 (oriented_segment_factor_dimension a)
    (@oriented_segment_factor_domain R a) (@oriented_segment_factor_open R a) (oriented_segment_factor_end a).

(** Source for [oriented_segment_factor_boundary]: the
    original segment boundary is the negative of
    the printed endpoint difference, supporting the
    one-based sign in Federer 4.1.8, p. 362. *)
Lemma oriented_segment_factor_boundary (R:realType) (h2:(1+1:R)!=0) (a:oriented_segment_factor R):
  @current_boundary R h2 (oriented_segment_factor_dimension a) 0%N
    (@oriented_segment_factor_domain R a) (@oriented_segment_factor_open R a)
    (@oriented_segment_factor_current R h2 a)=
    -(@oriented_segment_factor_endpoint_difference R h2 a).
Proof.
rewrite /oriented_segment_factor_current oriented_segment_current_boundary
  /oriented_segment_factor_endpoint_difference opprB;by [].
Qed.
