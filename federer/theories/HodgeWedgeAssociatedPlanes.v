(** Federer (1969), 3.2.48, p. 286: the starred-word norm
    depends on the actual unit tangent planes, rather than their chosen
    orientations. Supporting direct use of 1.7.11, p. 36, with its
    operator-norm uniqueness and positive normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ModuleQuotient SubspaceCarrier SubspaceEquality LinearBasis
  InnerProductUP InnerProductRestriction ProductInner AssociatedSubspace SimpleElementary
  ExteriorGrading ExteriorNorm ExteriorMaps ExteriorHomogeneousProducts InnerExteriorPositivity
  HodgeMaps SubspaceDifference SubspaceDifferenceNorm OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hodge_wedge_associated_planes]: independence of the
    two locally chosen unit tangent words in 3.2.48, p. 286. Two
    applications of the actual subspace-difference formula identify the
    same operator norm, including singular and zero-degree cases. *)
Theorem hodge_wedge_associated_planes (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) B (hV:@is_inner_product R V B) d (b:'I_d->V) (hb:is_basis b)
    (E:exterior_power V d) (hE:exterior_norm h2 hV E= 1)
    k m (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (x x':exterior_power V k) (y y':exterior_power V m):
  simple x ->simple x' ->simple y ->simple y' ->
  exterior_norm h2 hV x= 1 ->exterior_norm h2 hV x'= 1 ->
  exterior_norm h2 hV y= 1 ->exterior_norm h2 hV y'= 1 ->
  (forall v,FedererSimple.T x v <->FedererSimple.T x' v) ->
  (forall v,FedererSimple.T y v <->FedererSimple.T y' v) ->
  exterior_norm h2 hV (exterior_product (hodge_vector h2 hV E hk x) (hodge_vector h2 hV E hm y))=
  exterior_norm h2 hV (exterior_product (hodge_vector h2 hV E hk x') (hodge_vector h2 hV E hm y')).
Proof.
move=>hsX hsX' hsY hsY' hX hX' hY hY' hSX hTY.
have hS:FedererSimple.T x=FedererSimple.T x':=subspace_ext hSX.
have hT:FedererSimple.T y=FedererSimple.T y':=subspace_ext hTY.
have hFirst:=@subspace_difference_norm R h2 V B hV d b hb E hE k m hk hm hkm x y hsX hsY hX hY.
have hSecond:=@subspace_difference_norm R h2 V B hV d b hb E hE k m hk hm hkm x' y' hsX' hsY' hX' hY'.
rewrite hS hT in hFirst.
have hEqual:=operator_norm_unique hFirst hSecond.
have hNonzero:(Num.sqrt (2:R))^+(k+m-d)!=0.
  have hs:Num.sqrt (2:R)!=0 by rewrite gt_eqF // sqrtr_gt0 ltr0n.
  by rewrite expf_eq0 (negPf hs) andbF.
exact (mulfI hNonzero hEqual).
Qed.
