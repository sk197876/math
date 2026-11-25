(** Federer (1969), 4.1.5, pp. 349–350: independent
    laws of the linear extension of S to the original
    compact continuous vector fields. Existence and an
    opaque selection are separate from this specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP CompactContinuousDomainFields CompactUniformApproximationUP PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_distribution_continuous_extension]: T
    is linear, agrees with S on original tests and
    is the scalar limit of every original compact uniform
    test approximation, as in Federer 4.1.5, pp. 349–350.
    The sharp variation bound is proved later. *)
Record is_distribution_continuous_extension (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (S:Hom E R^o) (T:(X->Y)->R):Prop:={
  (** Source for [distribution_extension_add]: additivity
      of T on the original D, Federer 4.1.5, p. 349. *)
  distribution_extension_add:forall w v,
    compact_continuous_domain_fields U hNY w ->
    compact_continuous_domain_fields U hNY v ->
    T (fun x=>w x+v x)=T w+T v;
  (** Source for [distribution_extension_scale]: homogeneity
      of T on the original D, Federer 4.1.5, p. 349. *)
  distribution_extension_scale:forall c w,
    compact_continuous_domain_fields U hNY w ->
    T (fun x=>c*:w x)=c*T w;
  (** Source for [distribution_extension_original]: T extends
      the actual test functional S, Federer 4.1.5, p. 349. *)
  distribution_extension_original:forall phi:E,T (value phi)=S phi;
  (** Source for [distribution_extension_limit]: the original
      convolution limit of Federer 4.1.5, p. 349,
      independently of the particular actual approximation. *)
  distribution_extension_limit:forall w,
    compact_continuous_domain_fields U hNY w ->
    forall P:R->E,is_compact_uniform_test_approximation U NY value w P ->
    positive_norm_limit (fun a:R^o=>`|a|) (fun e=>S (P e)) (T w)
}.
