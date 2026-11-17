(** Supporting algebra for Federer (1969), 3.4.8(8), p. 329,
    used in the auxiliary coefficient argument for (5), p. 328.
    A finite module over the original domain admits a scalar
    functional nonzero on any non-torsion vector. Reuse the finite
    free cover, existing field quotient, separation and denominator
    clearing. The module itself need not be torsion free. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import Hom RingSubmoduleUP RingFiniteSynthesis
  FractionFieldUP CommutativeDomainUP FiniteModuleFreeCover FractionFreeSeparation
  FractionFreeFunctionalDenominator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_module_nontorsion_functional]: supporting
    finite original coefficient-module connection for Federer 3.4.8(8),
    p. 329 and the auxiliary sentence in (5), p. 328. A non-torsion
    vector is detected by an original-domain-valued linear functional.
    No basis, projectivity or torsion-free module premise is added. *)
Theorem finite_module_nontorsion_functional (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) (V:lmodType A) (x:V):
  is_commutative_fraction_field embed ->is_commutative_integral_domain A ->
  is_finitely_generated_ring_submodule (setT:set V) ->
  (forall a:A,a*:x = 0 ->a = 0) ->
  exists L:{linear V->A^o},L x<>0.
Proof.
move=>hField hDomain hFinite hTorsion.
have [n [e hCover]]:=finite_module_free_cover hFinite.
pose U:=[the lmodType A of {ffun 'I_n->A^o}].
pose f:{linear U->V}:=GRing.Linear.clone _ _ _ _ (@ring_finite_synthesis A V n e) _.
have hOnto v:exists a:U,f a = v:=hCover v.
have [b hb]:=hOnto x.
have hTorsionB a:a*:(f b) = 0 ->a = 0 by rewrite hb;exact:hTorsion a.
have [ell [hEll hKernel]]:=@fraction_free_separating_functional A K embed V n f b
  hField hDomain hTorsionB.
have [d [h [hd hDenominator]]]:=@fraction_free_functional_denominator A K embed n ell hField hDomain.
have hInjective:=fraction_field_embedding_injective hField.
have hKill a:f a = 0 ->h a = 0.
  move=>hA;apply:hInjective;rewrite rmorph0 hDenominator (hKernel a hA) mulr0.
  reflexivity.
have hB:h b<>0.
  move=>hZero;apply:hd;apply:hInjective.
  have hh:=hDenominator b;rewrite hZero rmorph0 hEll mulr1 in hh.
  rewrite rmorph0;exact:esym hh.
have [lift hLift]:=choice hOnto.
pose value(v:V):=h (lift v).
have hSame a c:f a = f c ->h a = h c.
  move=>hEqual;apply:subr0_eq;rewrite -linearB;apply:hKill.
  by rewrite linearB hEqual subrr.
have hFactor a:value (f a) = h a:=hSame (lift (f a)) a (hLift (f a)).
have hLinear:linear value.
  move=>c v w.
  have hVector:f (c*:lift v+lift w) = c*:v+w.
    by rewrite linearP /= !hLift.
  have hEquality:value (c*:v+w) = h (c*:lift v+lift w).
    apply:hSame;by rewrite hLift hVector.
  by rewrite hEquality linearP.
pose L:{linear V->A^o}:=HB.pack value (GRing.isLinear.Build A V A^o *:%R value hLinear).
exists L;change (value x<>0);rewrite -hb hFactor;exact:hB.
Qed.
