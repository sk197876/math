(** Federer (1969), 3.4.12, p. 339: actual holomorphic
    chart inversion, composition and open target restriction.
    Use the proved holomorphic chain and restriction laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormDifferentialUP
  NormOpenDomainLaws HolomorphicUP HolomorphicFiniteCalculus HolomorphicTranslations
  HolomorphicDiffeomorphismUP HolomorphicDiffeomorphismRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Operations.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.

(** Source for [holomorphic_diffeomorphism_inverse_laws]: interchange
    the two actual holomorphic chart maps and their original domains,
    as allowed by the definition in 3.4.12, p. 339. *)
Lemma holomorphic_diffeomorphism_inverse_laws A B f g:
  is_holomorphic_diffeomorphism hNX A B f g ->is_holomorphic_diffeomorphism hNX B A g f.
Proof. move=>[hF hG hMaps hInverseMaps hLeft hRight];by constructor. Qed.

(** Source for [holomorphic_diffeomorphism_composition]: compose
    original chart maps, retaining the actual inverse and exact domains,
    as used in the complex extension in 3.4.12, p. 339. *)
Lemma holomorphic_diffeomorphism_composition A B C f g s t:
  is_holomorphic_diffeomorphism hNX A B f g ->
  is_holomorphic_diffeomorphism hNX B C s t ->
  is_holomorphic_diffeomorphism hNX A C (fun x=>s (f x)) (fun y=>g (t y)).
Proof.
move=>hD hE;constructor.
- exact:holomorphic_compose_on (holomorphic_diffeomorphism_maps hD)
    (holomorphic_diffeomorphism_forward hD) (holomorphic_diffeomorphism_forward hE).
- exact:holomorphic_compose_on (holomorphic_diffeomorphism_inverse_maps hE)
    (holomorphic_diffeomorphism_inverse hE) (holomorphic_diffeomorphism_inverse hD).
- move=>x hx;exact:(@holomorphic_diffeomorphism_maps R X NX hNX B C s t hE (f x)
    (@holomorphic_diffeomorphism_maps R X NX hNX A B f g hD x hx)).
- move=>y hy;exact:(@holomorphic_diffeomorphism_inverse_maps R X NX hNX A B f g hD (t y)
    (@holomorphic_diffeomorphism_inverse_maps R X NX hNX B C s t hE y hy)).
- move=>x hx;rewrite (@holomorphic_diffeomorphism_left_inverse R X NX hNX B C s t hE (f x)
    (@holomorphic_diffeomorphism_maps R X NX hNX A B f g hD x hx)).
  exact:(@holomorphic_diffeomorphism_left_inverse R X NX hNX A B f g hD x hx).
- move=>y hy;rewrite (@holomorphic_diffeomorphism_right_inverse R X NX hNX A B f g hD (t y)
    (@holomorphic_diffeomorphism_inverse_maps R X NX hNX B C s t hE y hy)).
  exact:(@holomorphic_diffeomorphism_right_inverse R X NX hNX B C s t hE y hy).
Qed.

(** Source for [holomorphic_diffeomorphism_target_restriction]: an
    original open target subset has the original inverse-image domain,
    supporting the local chart changes in 3.4.12, p. 339. *)
Lemma holomorphic_diffeomorphism_target_restriction A B W f g:
  is_holomorphic_diffeomorphism hNX A B f g ->
  (forall y,W y ->B y) ->(forall y,W y ->@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX W y) ->
  is_holomorphic_diffeomorphism hNX (fun x=>A x /\W (f x)) W f g.
Proof.
move=>hD hWB hW.
exact:holomorphic_diffeomorphism_inverse_laws
  (holomorphic_diffeomorphism_source_restriction (holomorphic_diffeomorphism_inverse_laws hD) hWB hW).
Qed.

(** Source for [holomorphic_translation_diffeomorphism]: the actual
    translations are inverse holomorphic charts on the whole source,
    including zero dimension, in 3.4.12, p. 339. *)
Lemma holomorphic_translation_diffeomorphism c:
  is_holomorphic_diffeomorphism hNX (fun _=>True) (fun _=>True)
    (fun x=>x-c) (fun y=>y+c).
Proof.
have [hPlus hMinus]:=@holomorphic_translations R X NX hNX (fun _=>True)
  (fun x _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX x) c.
constructor=>//.
- by move=>x _;rewrite subrK.
- by move=>y _;rewrite addrK.
Qed.
End Operations.
