(** Federer (1969), 4.1.1, p. 345: restriction
    is continuous on smooth-function spaces for the
    original compact derivative topologies. No derivative
    order or compact carrier changes in the estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP DirectedSeminormFamilyUP SeminormFamilyLinearContinuity
  SmoothCompactSet SmoothCompactDomainInclusion SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP
  SmoothFunctionSeminormFamily SmoothFunctionTopology SmoothRestrictionUP SmoothRestrictionDerivatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section RestrictionContinuity.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Hypothesis hUV:forall x,U x ->V x.
Variables A B:lmodType R.
Variable evA:A->X->Y.
Variable evB:B->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variables DA:forall k,X->Hom A (Z k).
Variables DB:forall k,X->Hom B (Z k).
Hypothesis hDA:@is_smooth_function_derivatives R X Y NX NY hNX hNY U A evA DA.
Hypothesis hDB:@is_smooth_function_derivatives R X Y NX NY hNX hNY V B evB DB.
Variable L:Hom B A.
Hypothesis hL:is_smooth_restriction U evA evB L.
Local Notation IA := (nat*smooth_compact_set hNX U)%type.
Local Notation IB := (nat*smooth_compact_set hNX V)%type.
Local Notation nuA := (smooth_function_derivative_seminorm hDA).
Local Notation nuB := (smooth_function_derivative_seminorm hDB).
Local Notation p := (fun j:IB=>nuB j.2 j.1).
Local Notation q := (fun j:IA=>nuA j.2 j.1).
Local Notation hp := (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hDB)).

(** Source for [smooth_restriction_continuous]: the actual
    restriction E(V,Y) to E(U,Y) is continuous,
    supporting the compact-support dual extension of
    Federer 4.1.1, p. 345. *)
Theorem smooth_restriction_continuous:
  open_family_continuous (smooth_function_opens hDB) (smooth_function_opens hDA) L.
Proof.
apply:(@seminorm_family_bounded_linear_continuous R B A IB IA p q
  (smooth_function_opens hDB) (smooth_function_opens hDA) hp
  (smooth_function_topology_laws hDB) (smooth_function_topology_laws hDA) L).
move=>[i K].
pose KV:=@smooth_compact_domain_inclusion R X NX hNX U V hUV K.
exists (i,KV),1; split; first exact:ler01.
move=>f; rewrite mul1r.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U A DA K i (nuA K i)
  (smooth_function_derivative_seminorm_laws hDA K i) (L f) (nuB KV i f)
  (smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hDB KV i) f))=>j hj x hx.
rewrite (@smooth_restriction_higher_derivative R X Y NX NY hNX hNY U V hU hUV A B evA evB
  DA DB hDA hDB L hL j f x (smooth_compact_in_domain K x hx)).
exact:(smooth_derivative_seminorm_bound (smooth_function_derivative_seminorm_laws hDB KV i) f hj hx).
Qed.
End RestrictionContinuity.
