(** Private proved sequence witness for Federer (1969), 3.1.20,
    p. 232. Downstream proofs use the sealed sequence laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormRegularity NormRegularityOperations
  LocalRetractionUP RetractionPatchUP RetractionPatchingUP RetractionPatchingStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Construction.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables (B U:set X) (P Q:nat->set X) (k:nat).
Hypothesis hF:is_retraction_patch_family hNX hNY B U P Q k.

(** Source for [retraction_patch_family_next]: the successor
    construction of W_i,f_i on Federer 3.1.20, p. 232, with
    the intermediate-map correction in the erratum p. 4, book
    p. 232 line 11. Empty enumeration slots leave the state fixed. *)
Lemma retraction_patch_family_next i (W:set X) (f:X->X) :
  is_partial_neighbourhood_retraction hNX B W f k -> W `<=` U ->
  exists W' f',is_retraction_sequence_step hNX B U (P i) (Q i) W W' f f' k.
Proof.
move=>hpartial hWU.
have hPi:=@patch_family_closed R X Y NX NY hNX hNY B U P Q k hF i.
have hQi:=@patch_family_open R X Y NX NY hNX hNY B U P Q k hF i.
have hQU:=@patch_family_inside R X Y NX NY hNX hNY B U P Q k hF i.
case:(@patch_family_charts R X Y NX NY hNX hNY B U P Q k hF i)=>[[hPe hQe]|[T [V [phi [psi [u hdata]]]]]].
- exists W,f; constructor.
  + exact hpartial.
  + exact hWU.
  + by move=>x hn; split.
  + by move=>x hw hn.
  + by rewrite hQe setU0.
  + by rewrite hQe=>x [].
- have [hphi [hpsi [hphiV [him [hcan [hconv [hu [hrange [hPT [hQP [hu0 hu1]]]]]]]]]]]:=hdata.
  have [h [hp hm]]:=@retraction_patching_step R X Y NX NY hNX hNY
    B W T (P i) (Q i) V f phi psi u k hpartial hphi hpsi hphiV him hcan hconv
    hu hrange hPi hQi hPT hQP hu0 hu1.
  exists (retraction_patch_domain W T (P i) (Q i) f),h; constructor.
  + exact: retraction_patch_partial hp.
  + move=>x [[hx|hx]|hx]; [exact: hWU x hx.1|exact: hWU x hx.1|exact: hQU].
  + exact: retraction_patch_membership_off hp.
  + exact: retraction_patch_old_values hp.
  + exact: retraction_patch_fixed_set hp.
  + move=>x hx; by right.
Qed.

(** Source for [retraction_patching_sequence_exists]: the
    countable induction starting W_0=empty and f_0=0, Federer
    3.1.20, p. 232. A proved successor witness and elementary
    recursion supply a sequence satisfying the abstract laws. *)
Theorem retraction_patching_sequence_exists :
  exists p:((nat->set X)*(nat->X->X))%type,
    is_retraction_patching_sequence hNX B U P Q p.1 p.2 k.
Proof.
pose Pair:=(set X*(X->X))%type.
pose Spec:=fun p:Pair=>is_partial_neighbourhood_retraction hNX B p.1 p.2 k /\ p.1 `<=` U.
pose State:={p:Pair|Spec p}.
have hzero:is_partial_neighbourhood_retraction hNX B set0 (fun _=>0) k.
  constructor.
  - exact (@norm_class_constant R X X NX NX hNX hNX set0 0 k (fun x hx=>False_rect _ hx)).
  - by move=>x [].
  - by move=>x hb [].
have h0:Spec (set0,(fun _=>0:X)) by split=>// x [].
pose s0:State:=exist Spec (set0,(fun _=>0:X)) h0.
have hn (i:nat) (s:State):exists t:State,
    is_retraction_sequence_step hNX B U (P i) (Q i)
      (proj1_sig s).1 (proj1_sig t).1 (proj1_sig s).2 (proj1_sig t).2 k.
  have [W' [f' hnext]]:=retraction_patch_family_next i (proj2_sig s).1 (proj2_sig s).2.
  have ht:Spec (W',f').
    split; [exact: retraction_step_partial hnext|exact: retraction_step_inside hnext].
  exists (exist Spec (W',f') ht); exact hnext.
have hex (z:nat*State):exists t:State,
    is_retraction_sequence_step hNX B U (P z.1) (Q z.1)
      (proj1_sig z.2).1 (proj1_sig t).1 (proj1_sig z.2).2 (proj1_sig t).2 k.
  exact: hn.
have [step hstep]:=choice hex.
pose states:=fix loop (i:nat):State:=if i is j.+1 then step (j,loop j) else s0.
pose W:=fun i=>(proj1_sig (states i)).1.
pose f:=fun i=>(proj1_sig (states i)).2.
exists (W,f); constructor.
- by [].
- by move=>x.
- move=>i; exact (proj2_sig (states i)).1.
- move=>i; exact (proj2_sig (states i)).2.
- move=>i; exact: hstep (i,states i).
Qed.
End Construction.
