(** Federer (1969), 4.1.1, p. 345: the exact continuity
    criterion for distributions. The compact set in nu^i_K
    is the same K that supports the test function; both order
    and bound are nonnegative integers. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenTopology OpenFamilyTopologyUP
  FinalOpenTopologyUP DirectedSeminormFamilyUP SeminormFamilyRestriction SeminormRealDualBound
  ContinuousMultilinearSealed LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothFunctionSeminormFamily
  SmoothDerivativeSeminormUP SmoothDerivativeSupport SmoothTestSpaces SmoothTestTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section DistributionLocalContinuity.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation KIndex := (smooth_compact_set hNX U).
Local Notation I := (nat * KIndex)%type.
Local Notation DK := (smooth_fixed_test_space hE).
Local Notation DT := (smooth_test_space hE).
Local Notation k := (smooth_fixed_test_inclusion hE).
Local Notation j := (smooth_test_step hE).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation p := (fun i:I=>nu i.2 i.1).
Local Notation hp := (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hD)).
Local Notation PK := (@smooth_test_step_opens R X Y NX NY hNX hNY U E ev hE D hD).
Local Notation SO := (@smooth_test_opens R X Y NX NY hNX hNY U E ev hE D hD).
Local Notation RO := (norm_open_family (@scalar_absolute_value_norm R)).

(** Source for [distribution_continuity_local_bound]: the
    iff criterion for T belonging to D'(U,Y), Federer 4.1.1,
    p. 345, expressed with the equivalent absolute-value bound.
    The same original K is retained and no uniform order over
    different compact sets is imposed. *)
Theorem distribution_continuity_local_bound (L:Hom DT R^o):
  open_family_continuous SO RO L <-> forall K:KIndex,
    exists i M:nat,forall f:DK K,`|L (j K f)|<=M%:R * nu K i (k K f).
Proof.
have hFinal:=@smooth_test_final_topology_laws R X Y NX NY hNX hNY U E ev hE D hD.
have hStep K:=@restricted_seminorm_family_directed R E (DK K) I p hp (k K).
split.
- move=>hL K.
  pose LK:Hom (DK K) R^o:=hom_comp L (j K).
  have hLK:open_family_continuous (PK K) RO LK.
    exact:(@final_open_topology_mapping KIndex (fun K=>DK K) DT R^o
      PK (fun K f=>j K f) SO RO L hFinal).1 hL K.
  have [z [C [hC hb]]]:=(seminorm_real_linear_continuity_iff (hStep K)
    (@smooth_test_step_topology_laws R X Y NX NY hNX hNY U E ev hE D hD K) LK).1 hLK.
  exists z.1,(Num.bound C)=>f.
  have hf:=subspace_representation_member (smooth_fixed_test_space_laws hE K) f.
  have hCmp:=@smooth_supported_seminorm_bound R X Y NX NY hNX hNY U hU E ev hE D hD
    K z.2 z.1 (nu K z.1) (nu z.2 z.1)
    (smooth_function_derivative_seminorm_laws hD K z.1)
    (smooth_function_derivative_seminorm_laws hD z.2 z.1) (k K f) hf.
  have hReal:`|LK f|<=C * nu K z.1 (k K f):=
    le_trans (hb f) (ler_wpM2l hC hCmp).
  have hLarge:C<(Num.bound C)%:R:=archi_boundP hC.
  have hNat:=ler_wpM2r
    (smooth_derivative_seminorm_nonnegative
      (smooth_function_derivative_seminorm_laws hD K z.1) (k K f)) (ltW hLarge).
  exact:(le_trans hReal hNat).
- move=>hBounds.
  apply:(@final_open_topology_mapping KIndex (fun K=>DK K) DT R^o
    PK (fun K f=>j K f) SO RO L hFinal).2=>K.
  pose LK:Hom (DK K) R^o:=hom_comp L (j K).
  change (open_family_continuous (PK K) RO LK).
  apply:(seminorm_real_linear_continuity_iff (hStep K)
    (@smooth_test_step_topology_laws R X Y NX NY hNX hNY U E ev hE D hD K) LK).2.
  have [i [M hb]]:=hBounds K.
  exists (i,K),M%:R; split; first exact:ler0n.
  exact:hb.
Qed.
End DistributionLocalContinuity.
