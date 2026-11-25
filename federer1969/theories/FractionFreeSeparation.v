(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328,
    using the finite original coefficient module of (8), p. 329.
    Separate an original non-torsion vector after clearing denominators.
    The quotient and separating functional are the existing ones from
    Chapters 1 and 3; no localization existence is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import Hom ModuleQuotient PairingSeparation
  FractionFieldUP CommutativeDomainUP RingSubmoduleUP FractionFreeKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [fraction_free_separating_functional]: supporting
    finite-coefficient connection for Federer 3.4.8(8), p. 329 and
    the auxiliary sentence in (5), p. 328. A lift of a non-torsion
    vector admits a field functional equal to one there and zero on
    every embedded original kernel vector. No finite basis of the
    original ring module is assumed. *)
Theorem fraction_free_separating_functional (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) (V:lmodType A) n
    (f:{linear {ffun 'I_n->A^o}->V}) (b:{ffun 'I_n->A^o}):
  is_commutative_fraction_field embed ->is_commutative_integral_domain A ->
  (forall a:A,a*:(f b) = 0 ->a = 0) ->
  exists ell:Hom {ffun 'I_n->K^o} K^o,
    ell (fraction_free_coordinates embed b) = 1 /\
    forall a:{ffun 'I_n->A^o},f a = 0 ->
      ell (fraction_free_coordinates embed a) = 0.
Proof.
move=>hField hDomain hTorsion.
pose W:=[the lmodType K of {ffun 'I_n->K^o}].
pose N:=@fraction_free_kernel A K embed V n f.
have hN:is_ring_submodule N:=fraction_free_kernel_submodule f hField hDomain.
pose S:subspace W:=@Subspace K W N (ring_submodule_zero hN)
  (@ring_submodule_add K W N hN) (@ring_submodule_scale K W N hN).
pose Q:=[the lmodType K of module_quotient S].
pose pi:{linear W->Q}:=GRing.Linear.clone _ _ _ _ (@quotient_projection K W S) _.
pose v:=fraction_free_coordinates embed b.
have hNot:~N v:=@fraction_free_kernel_detects_torsion A K embed V n f b hField hTorsion.
have hNonzero:pi v!=0.
  apply/eqP=>hZero;apply:hNot.
  have hProjection:quotient_projection S v = quotient_projection S 0.
    change (pi v = pi 0);by rewrite hZero linear0.
  have hMembership:=(proj1 (@quotient_projection_eq K W S v 0)) hProjection.
  move:hMembership;by rewrite subr0.
have [psi hPsi]:=@nonzero_functional K Q (pi v) hNonzero.
pose ell:=hom_comp psi (hom_of_linear pi).
exists ell;split;first exact:hPsi.
move=>a hA.
have hMember:N (fraction_free_coordinates embed a).
  exists 1,a;split;first by apply/eqP;exact:oner_neq0.
  split=>// i;by rewrite rmorph1 mul1r /fraction_free_coordinates ffunE.
have hProjection:pi (fraction_free_coordinates embed a) = 0.
  change (quotient_projection S (fraction_free_coordinates embed a) = (0:Q)).
  rewrite -(linear0 (@quotient_projection K W S)).
  apply/quotient_projection_eq;by rewrite subr0.
change (psi (pi (fraction_free_coordinates embed a)) = 0).
by rewrite hProjection linear0.
Qed.
