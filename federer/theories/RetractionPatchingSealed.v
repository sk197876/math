(** Opaque proved patching-sequence witness for Federer (1969),
    3.1.20, p. 232. The implementation is private; downstream
    arguments use the initial, successor and retraction laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP RetractionPatchingUP RetractionPatchingConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type RETRACTION_PATCHING.
(** Source for [value]: the sequence W_i,f_i in Federer
    3.1.20, p. 232, specified by its abstract patching laws.
    The implementation must prove existence from the chart data. *)
Parameter value : forall (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (B U:set X) (P Q:nat->set X) k,
  is_retraction_patch_family hNX hNY B U P Q k ->
  ((nat->set X)*(nat->X->X))%type.
(** Source for [laws]: the proved start, successor and corrected
    intermediate-map invariants of 3.1.20, p. 232, erratum
    p. 4, book p. 232 line 11. *)
Parameter laws : forall (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (B U:set X) (P Q:nat->set X) k
  (hF:is_retraction_patch_family hNX hNY B U P Q k),
  let s:=@value R X Y NX NY hNX hNY B U P Q k hF in
  is_retraction_patching_sequence hNX B U P Q s.1 s.2 k.
End RETRACTION_PATCHING.

Module RetractionPatching : RETRACTION_PATCHING.
(** Source for [chosen]: private selection from the proved
    sequence existence for 3.1.20, p. 232. No choice or proof
    is postulated by the public signature. *)
Definition chosen (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (B U:set X) (P Q:nat->set X) k
    (hF:is_retraction_patch_family hNX hNY B U P Q k) :=
  cid (@retraction_patching_sequence_exists R X Y NX NY hNX hNY B U P Q k hF).
(** Source for [value]: the hidden proved witness W_i,f_i
    for the induction of Federer 3.1.20, p. 232. *)
Definition value (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (B U:set X) (P Q:nat->set X) k
    (hF:is_retraction_patch_family hNX hNY B U P Q k) :=
  projT1 (@chosen R X Y NX NY hNX hNY B U P Q k hF).
(** Source for [laws]: the private witness satisfies the
    public patching-sequence laws of 3.1.20, p. 232. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (B U:set X) (P Q:nat->set X) k
    (hF:is_retraction_patch_family hNX hNY B U P Q k) :
  let s:=@value R X Y NX NY hNX hNY B U P Q k hF in
  is_retraction_patching_sequence hNX B U P Q s.1 s.2 k.
Proof. exact (projT2 (@chosen R X Y NX NY hNX hNY B U P Q k hF)). Qed.
End RetractionPatching.
