(** Federer (1969), 3.4.7, p. 325: the
    pullback from the original transverse kernel is a
    ring monomorphism. Its actual bounded linear inclusion
    is the analytic section through the origin. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormAnalyticLinear
  WeierstrassTransverseUP WeierstrassTransversePullback AnalyticPullbackInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_transverse_ring_monomorphism]:
    the original ring monomorphism in 3.4.7,
    p. 325. The proof uses only the
    sealed inclusion, projection and boundedness laws. *)
Theorem weierstrass_transverse_ring_monomorphism (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection):
  injective (@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
    v xi inclusion projection hSplit).
Proof.
have hInclusion:=@norm_bounded_linear_analytic R K X NK NX hNK hNX setT
  (fun z _=>norm_full_domain_interior NK z) inclusion
  (weierstrass_transverse_inclusion_bounded hSplit).
apply:(@analytic_ring_pullback_injective_section R X K NX NK hNX hNK setT setT
  projection inclusion 0
  (@weierstrass_transverse_projection_analytic R X K NX NK hNX hNK
    v xi inclusion projection hSplit) (hInclusion (projection 0) Logic.I)).
- exact:weierstrass_transverse_left_inverse hSplit.
- by rewrite !linear0.
Qed.
