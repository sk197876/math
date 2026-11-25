(** Federer (1969), 3.3.2, p. 287: the set of
    parameters whose cone contains a given compact C is open
    in the printed positive-aperture parameter domain. Empty
    compact sets are retained explicitly in the tube argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology num_normedtype.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  TopologicalProductMaps CompactProductTube StructureCone StructureProjectionKernel
  StructureConeJointOpen.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_compact_cone_containment_open]:
    the first displayed set in the proof of Federer
    3.3.2, p. 287, for every actual compact C.
    The positive-aperture restriction is written explicitly,
    so the statement is an ambient open-set assertion. *)
Theorem structure_compact_cone_containment_open (R:realType) n m
    (hmn:(m<=n)%N)
    (C:set (inner_metric_space (@euclidean_inner_productP R n))):
  compact C ->
  @open ((inner_metric_space (@euclidean_inner_productP R n)*
    euclidean_projection_space R n m)*(R^o*R^o))%type
    [set q|0<q.2.2 /\ C `<=`
      structure_cone (structure_projection_kernel hmn q.1.2)
        q.1.1 (q.2.1)%:E q.2.2].
Proof.
move=>hC.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose P:=(E*euclidean_projection_space R n m)%type.
pose Q:=(P*(R^o*R^o))%type.
pose S:set Q:=[set q|0<q.2.2].
have hS:open S.
  have hf:continuous (fun q:Q=>(q.2.2:R^o)).
    move=>q; exact:(continuous_comp (@second_projection_continuous P (R^o*R^o)%type q)
      (@second_projection_continuous R^o R^o q.2)).
  exact:((continuousP (fun q:Q=>(q.2.2:R^o))).1 hf
    [set t:R^o|0<t] (@open_gt R 0)).
pose U:set (Q*E):=[set z|0<z.1.2.2 /\
  structure_cone (structure_projection_kernel hmn z.1.1.2)
    z.1.1.1 (z.1.2.1)%:E z.1.2.2 z.2].
have hU:open U:=@structure_positive_joint_cone_open R n m hmn.
rewrite openE=>q [hs hContain].
have hCU:forall x,C x ->U (q,x) by move=>x hx; split=>//; exact:hContain.
have [V [W [hV [hq [_ [hCW hTube]]]]]]:=compact_product_open_tube hC hU hCU.
have hVS:open (V `&` S):=openI hV hS.
have hqVS:(V `&` S) q by split.
have hn:nbhs q (V `&` S) by rewrite openE in hVS; exact:(hVS q hqVS).
apply:(@filterS _ (nbhs q) _ (V `&` S) _ _ hn)=>p [hp hsp].
split=>// x hx; exact:(hTube (p,x) (conj hp (hCW x hx))).2.
Qed.
