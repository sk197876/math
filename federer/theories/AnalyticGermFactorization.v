(** Federer (1969), 3.4.7, p. 325: the
    original finite-dimensional analytic germ ring has unique
    factorization at every centre. Actual analytic translations
    transfer the origin theorem through a proved isomorphism. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws NormAnalyticUP
  NormAnalyticTranslation LinearBasis AnalyticGermRing CommutativeFactorizationUP
  CommutativeFactorizationIsomorphism AnalyticPullbackRingMorphism AnalyticPullbackSurjection
  AnalyticPullbackInjection AnalyticGermFactorizationOrigin.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_germ_ring_factorization]:
    the full original unique-factorization assertion of
    3.4.7, p. 325. The centre is arbitrary,
    dimension zero remains, and a finite source basis
    expresses the original finite-dimensional premise. Actual
    analytic pullbacks prove both directions of the translation. *)
Theorem finite_analytic_germ_ring_factorization (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) a:
  is_basis e ->is_unique_factorization_commutative_domain
    [the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Proof.
move=>he.
have hTranslations:=@norm_translations_analytic R X NX hNX setT
  (fun x _=>norm_full_domain_interior NX x) a.
pose u:=fun x:X=>x-a.
pose v:=fun x:X=>x+a.
have hu:@norm_analytic_at R X X NX NX hNX hNX setT u a:=hTranslations.2 a Logic.I.
have hv:@norm_analytic_at R X X NX NX hNX hNX setT v (u a):=hTranslations.1 (u a) Logic.I.
pose M:=@analytic_germ_ring_pullback R X X NX NX hNX hNX setT u a hu.
have hLeft x:v (u x) = x by rewrite /u /v subrK.
have hRight x:u (v x) = x by rewrite /u /v addrK.
have hPoint:v (u a) = a:=hLeft a.
have hSurjective:=@analytic_ring_pullback_surjective_left_inverse R X X NX NX hNX hNX
  setT setT u v a hu hv hLeft.
have hInjective:=@analytic_ring_pullback_injective_section R X X NX NX hNX hNX
  setT setT u v a hu hv hRight hPoint.
have hOrigin:=@finite_analytic_germ_factorization_at_origin R n X NX hNX e he.
have hA:is_unique_factorization_commutative_domain
    [the comNzRingType of (@analytic_germ_ring R X NX hNX (u a))].
  by rewrite /u subrr.
exact:(commutative_isomorphism_factorization hInjective hSurjective hA).
Qed.
