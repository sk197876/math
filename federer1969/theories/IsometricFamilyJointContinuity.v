(** Federer (1969), 3.3.4, p. 290: continuity
    of the projective isometric action. This general
    metric argument promotes continuous point orbits
    to joint continuity using the common isometry
    law in the second variable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [isometric_family_joint_continuous]:
    supporting joint topology of the actual action
    on T(U) in Federer 3.3.4, p. 290.
    A triangle estimate splits the target radius
    between the point orbit and the source point. *)
Theorem isometric_family_joint_continuous (R:realType) (P:topologicalType)
    (X:metricType R) (A:P->X->X):
  (forall p x y,mdist (A p x) (A p y)=mdist x y) ->
  (forall x,continuous (fun p=>A p x)) ->
  continuous (fun z:P*X=>A z.1 z.2).
Proof.
move=>hIso hOrbit [p x] U hU.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (A p x) U) hU.
have hHalf:0<e/2 by rewrite divr_gt0 // ltr0n.
have hTarget:nbhs (A p x) [set y|mdist (A p x) y<e/2].
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (A p x) _)).
  by exists (e/2).
have hP:nbhs p [set q|mdist (A p x) (A q x)<e/2]:=hOrbit x p _ hTarget.
have hX:nbhs x [set y|mdist x y<e/2].
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP x _)).
  by exists (e/2).
exists ([set q|mdist (A p x) (A q x)<e/2],[set y|mdist x y<e/2]); first by split.
move=>[q y] [hq hy]; apply:hBall.
change (is_true (mdist (A p x) (A q y)<e)).
apply:le_lt_trans (metric_triangle (A p x) (A q x) (A q y)) _.
rewrite hIso.
have hSum:e/2+e/2=e by field.
have h:=ltrD hq hy; by rewrite hSum in h.
Qed.
