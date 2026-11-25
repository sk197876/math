(** Federer (1969), 3.4.7, p. 325: the
    original analytic germ ring is Noetherian at every
    centre. Actual translations transfer the proved origin
    induction; no ring isomorphism is assumed as a hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws NormAnalyticUP
  NormAnalyticTranslation LinearBasis AnalyticGermRing CommutativeIdealUP NoetherianRingSurjection
  AnalyticPullbackRingMorphism AnalyticPullbackSurjection AnalyticGermNoetherianOrigin.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_germ_ring_noetherian]:
    the full original Noetherian assertion of 3.4.7,
    p. 325. The original centre is arbitrary,
    and the zero-dimensional case remains. The finite
    basis states precisely finite source dimension; no
    regular direction, preparation or ideal generators
    are supplied as additional premises. *)
Theorem finite_analytic_germ_ring_noetherian (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) a:
  is_basis e ->is_noetherian_commutative_ring
    [the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Proof.
move=>he.
have hTranslations:=@norm_translations_analytic R X NX hNX setT
  (fun x _=>norm_full_domain_interior NX x) a.
pose u:=fun x:X=>x-a.
pose v:=fun x:X=>x+a.
have hu:@norm_analytic_at R X X NX NX hNX hNX setT u a:=hTranslations.2 a Logic.I.
have hv:@norm_analytic_at R X X NX NX hNX hNX setT v (u a):=hTranslations.1 (u a) Logic.I.
pose embed:=@analytic_germ_ring_pullback R X X NX NX hNX hNX setT u a hu.
have hInverse x:v (u x) = x by rewrite /u /v subrK.
have hSurjective:=@analytic_ring_pullback_surjective_left_inverse R X X NX NX hNX hNX
  setT setT u v a hu hv hInverse.
have hOrigin:=@finite_analytic_germ_noetherian_at_origin R n X NX hNX e he.
have hA:is_noetherian_commutative_ring
    [the comNzRingType of (@analytic_germ_ring R X NX hNX (u a))].
  by rewrite /u subrr.
exact:(noetherian_ring_surjective_image hSurjective hA).
Qed.
