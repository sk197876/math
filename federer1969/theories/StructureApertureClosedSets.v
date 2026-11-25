(** Federer (1969), 3.3.8, p. 295: the actual closed
    increasing sets C_j of uniformly bounded conical mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructureConeDensityUP StructureConeCostOpen TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_aperture_bound_centres]: the sets C_j
    in Federer 3.3.8, p. 295, with the positive normalization
    absorbed into the independent real bound b. Every real radius
    and aperture in the original open ranges is retained. *)
Definition structure_aperture_bound_centres (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (delta t b:R):=
  [set x:inner_metric_space (@euclidean_inner_productP R n)|
    forall r s:R,0<r<delta ->0<s<t ->
      (structure_cone_cost hmn phi E (x,p) r s<=b%:E)%E].

(** Source for [structure_aperture_bound_centres_closed]: the
    assertion that each C_j is closed in Federer 3.3.8, p. 295,
    from the proof of 3.3.2, pp. 287–288. Every fixed normalized
    cost has open strict superlevels on the actual centre space;
    arbitrary intersections of their complements are closed.
    No original source measurability or finiteness is required. *)
Theorem structure_aperture_bound_centres_closed (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (delta t b:R):
  is_structure_measure phi ->closed (structure_aperture_bound_centres hmn phi E p delta t b).
Proof.
move=>hPhi.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose C r s:set X:=[set x|0<r<delta ->0<s<t ->
  (structure_cone_cost hmn phi E (x,p) r s<=b%:E)%E].
have hEqual:structure_aperture_bound_centres hmn phi E p delta t b=
    \bigcap_r \bigcap_s C r s.
  apply/seteqP; split=>x hx.
  - by move=>r _ s _; exact:hx r s.
  - by move=>r s; exact:hx r Logic.I s Logic.I.
rewrite hEqual; apply:closed_bigI=>r _; apply:closed_bigI=>s _.
case:(pselect (0<r<delta))=>hr; last first.
  have hT:C r s=setT by apply/seteqP; split=>// x _ hR; exfalso; exact:hr hR.
  by rewrite hT; exact:closedT.
case:(pselect (0<s<t))=>hs; last first.
  have hT:C r s=setT by apply/seteqP; split=>// x _ _ hS; exfalso; exact:hs hS.
  by rewrite hT; exact:closedT.
have hPair:continuous (fun x:X=>(x,p)).
  apply:topological_pair_continuous; [by move=>x; exact:cvg_id|exact:cst_continuous].
have hOpen:open [set x:X|(b%:E<structure_cone_cost hmn phi E (x,p) r s)%E].
  exact:(open_comp (fun x _=>hPair x) (@structure_cone_cost_superlevel_open R n m hmn phi E r s b
    hPhi (andP hr).1 (andP hs).1)).
have hC:C r s=~` [set x:X|(b%:E<structure_cone_cost hmn phi E (x,p) r s)%E].
  apply/seteqP; split=>x.
  - move=>hx hBad; have hLe:=hx hr hs; have hBadBound:=lt_le_trans hBad hLe.
    by rewrite ltxx in hBadBound.
  - move=>hx _ _; rewrite leNgt; exact/negP.
rewrite hC; exact:open_closedC hOpen.
Qed.

(** Source for [structure_aperture_bound_centres_mono]: the
    increasing C_j assertion in Federer 3.3.8, p. 295. Shrinking
    the aperture range weakens the same original cost condition. *)
Lemma structure_aperture_bound_centres_mono (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (delta t u b:R):
  u<=t ->structure_aperture_bound_centres hmn phi E p delta t b `<=`
    structure_aperture_bound_centres hmn phi E p delta u b.
Proof.
move=>hut x hx r s hr /andP [hs hsu]; apply:hx=>//.
apply/andP; split=>//; exact:lt_le_trans hsu hut.
Qed.
