(** Federer (1969), 4.1.7, p. 359:
    precomposition by a fixed original
    smooth map is continuous on the
    actual E spaces. The proof uses
    the original compact derivative seminorms;
    it makes no assertion about joint
    vector continuity of the final test
    topology S. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  ContinuousMultilinearSealed SmoothCompactSet SmoothCompactImage SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothDerivativeSeminormLaws
  SmoothFunctionSeminormFamily DirectedSeminormFamilyUP SeminormFamilyLinearContinuity
  SmoothPrecompositionUP SmoothPrecompositionSeminormBound OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section SmoothPrecompositionContinuity.
Variable R:realType.
Variables X Y T:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NT:T->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT).
Variables (A:X->Prop) (B:Y->Prop).
Variables E F:lmodType R.
Variables (ev:E->Y->T) (fv:F->X->T).
Hypothesis hE:is_smooth_function_space hNY hNT B ev.
Local Notation W := (fun j=>@ContinuousMultilinear.space R j Y T NY NT hNY hNT).
Local Notation V := (fun j=>@ContinuousMultilinear.space R j X T NX NT hNX hNT).
Variable D:forall j,Y->Hom E (W j).
Variable G:forall j,X->Hom F (V j).
Hypothesis hD:@is_smooth_function_derivatives R Y T NY NT hNY hNT B E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X T NX NT hNX hNT A F fv G.
Variable f:X->Y.
Hypothesis hImage:forall x,A x->B (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY A f.
Variable P:Hom E F.
Hypothesis hP:is_smooth_precomposition A ev fv f P.
Local Notation image := (@smooth_compact_image R X Y NX NY hNX hNY A B f hImage
  (@norm_class_continuous R X Y NX NY hNX hNY A f 0%N (hf 0%N))).
Local Notation I := (nat*smooth_compact_set hNY B)%type.
Local Notation J := (nat*smooth_compact_set hNX A)%type.
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation mu := (smooth_function_derivative_seminorm hG).
Local Notation p := (fun z:I=>nu z.2 z.1).
Local Notation q := (fun z:J=>mu z.2 z.1).
Local Notation hp := (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hD)).

(** Source for [smooth_precomposition_continuous]:
    the actual original precomposition map
    is continuous for the derivative-seminorm
    topologies of 4.1.1, pp. 343–344,
    supporting proper pushforward in Federer
    4.1.7, p. 359. *)
Theorem smooth_precomposition_continuous:
  open_family_continuous (smooth_function_opens hD) (smooth_function_opens hG) P.
Proof.
apply:(@seminorm_family_bounded_linear_continuous R E F I J p q
  (smooth_function_opens hD) (smooth_function_opens hG) hp
  (smooth_function_topology_laws hD) (smooth_function_topology_laws hG) P).
move=>[i K].
have [L [hL hBound]]:=@smooth_precomposition_seminorm_bound R X Y T NX NY NT
  hNX hNY hNT A B E F ev fv hE D G hD hG f hImage hf P hP K i
  (nu (image K) i) (mu K i) (smooth_function_derivative_seminorm_laws hD (image K) i)
  (smooth_function_derivative_seminorm_laws hG K i).
exists (i,image K),L;by split.
Qed.
End SmoothPrecompositionContinuity.
