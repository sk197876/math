(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    original analytic germ ring is Noetherian at every
    centre. Actual translations transfer the proved origin
    induction; no ring isomorphism is assumed as a hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP HolomorphicAtUP RealNormUP NormDifferentialUP NormOpenDomainLaws HolomorphicUP
  HolomorphicTranslations LinearBasis HolomorphicGermRing CommutativeIdealUP NoetherianRingSurjection
  HolomorphicPullbackRingMorphism HolomorphicPullbackSurjection HolomorphicGermNoetherianOrigin.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_germ_ring_noetherian]:
    the full original Noetherian assertion of 3.4.7,
    p. 325. The original centre is arbitrary,
    and the zero-dimensional case remains. The finite
    basis states precisely finite source dimension; no
    regular direction, preparation or ideal generators
    are supplied as additional premises. *)
Theorem finite_holomorphic_germ_ring_noetherian (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) n (e:'I_n->X) a:
  is_basis e ->is_noetherian_commutative_ring
    [the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)].
Proof.
move=>he.
have hTranslations:=@holomorphic_translations R X NX (complex_norm_real hNX) setT
  (fun x _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX x) a.
pose u:=fun x:X=>x-a.
pose v:=fun x:X=>x+a.
have hu:@is_holomorphic_at R X X NX NX (complex_norm_real hNX) (complex_norm_real hNX) setT u a.
  exists setT;split;first exact:Logic.I.
  split;first by move=>x _.
  exact:hTranslations.2.
have hv:@is_holomorphic_at R X X NX NX (complex_norm_real hNX) (complex_norm_real hNX) setT v (u a).
  exists setT;split;first exact:Logic.I.
  split;first by move=>x _.
  exact:hTranslations.1.
pose embed:=@holomorphic_germ_ring_pullback R X X NX NX (complex_norm_real hNX) (complex_norm_real hNX) setT u a hu.
have hInverse x:v (u x) = x by rewrite /u /v subrK.
have hSurjective:=@holomorphic_ring_pullback_surjective_left_inverse R X X NX NX (complex_norm_real hNX) (complex_norm_real hNX)
  setT setT u v a hu hv hInverse.
have hOrigin:=@finite_holomorphic_germ_noetherian_at_origin R n X NX hNX e he.
have hA:is_noetherian_commutative_ring
    [the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) (u a))].
  by rewrite /u subrr.
exact:(noetherian_ring_surjective_image hSurjective hA).
Qed.
