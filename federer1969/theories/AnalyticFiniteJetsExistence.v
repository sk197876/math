(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the existing finite-product universal property supplies
    actual finite-jet maps. Product extensionality proves
    uniqueness; every germ derivative remains unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormedFamilyUP NormedFamilySealed
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermRing
  AnalyticGermJetsSealed AnalyticFiniteJetsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_finite_jet_map_exists]: the
    finite derivative prefix from 3.4.5, p. 319,
    exists in the existing abstract product, supporting
    the ideal-closedness proof for 3.4.8(5), p. 328. *)
Theorem analytic_finite_jet_map_exists (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) m a:
  exists f:@analytic_germ_ring R X NX hNX a->@analytic_finite_jet_space R X NX hNX m,
    is_analytic_finite_jet_map f.
Proof.
pose Z:=fun i:'I_m=>@ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose N:=fun i:'I_m=>@ContinuousMultilinear.norm R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
have hP:=@NormedFamily.laws R m Z N.
have hEach alpha:exists u:@analytic_finite_jet_space R X NX hNX m,
    forall i,@analytic_finite_jet_coordinate R X NX hNX m i u =
      @AnalyticGermJets.value R X NX hNX a i alpha.
  have [u hu]:=normed_family_surjective hP [ffun i:'I_m=>@AnalyticGermJets.value R X NX hNX a i alpha].
  exists u=>i;by rewrite hu ffunE.
have [f hF]:=choice hEach;exists f;exact:hF.
Qed.

(** Source for [analytic_finite_jet_map_unique]: actual
    derivative coordinates determine the finite prefix map
    uniquely, supporting 3.4.8(5), p. 328, from
    the original derivative metric in 3.4.5, p. 319. *)
Lemma analytic_finite_jet_map_unique (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) m a
  (f g:@analytic_germ_ring R X NX hNX a->@analytic_finite_jet_space R X NX hNX m):
  is_analytic_finite_jet_map f ->is_analytic_finite_jet_map g ->f = g.
Proof.
move=>hf hg;apply:funext=>alpha.
apply:(normed_family_extensional (@NormedFamily.laws R m
  (fun i:'I_m=>@ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))
  (fun i:'I_m=>@ContinuousMultilinear.norm R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))))=>i.
by rewrite hf hg.
Qed.
