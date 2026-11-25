(** Federer (1969), 4.1.4, pp. 348–349: the smoothed
    density is constant on the connected component C_e.
    This supporting general-topology inference uses the
    original definition of connectedness and local constancy. *)
From mathcomp Require Import all_boot boolp functions classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [connected_local_constancy]: a locally constant
    function on the original connected set is constant, the
    inference for g_e on C_e in Federer 4.1.4, p. 349. *)
Theorem connected_local_constancy (X:topologicalType) (Y:Type)
    (A:set X) (f:X->Y):
  connected A ->
  (forall x,A x ->nbhs x [set z|A z /\ f z=f x]) ->
  forall a b,A a ->A b ->f b=f a.
Proof.
move=>hConnected hLocal a b ha hb.
pose C:set X:=[set x|A x /\ f x=f a].
pose D:set X:=[set x|A x /\ f x<>f a].
have hOpenC:open C.
  rewrite openE=>x [hx hEqual].
  apply:(filterS _ (hLocal x hx))=>z [hz hzx].
  split=>//; exact:etrans hzx hEqual.
have hOpenD:open D.
  rewrite openE=>x [hx hDifferent].
  apply:(filterS _ (hLocal x hx))=>z [hz hzx].
  split=>// hza; apply:hDifferent; exact:etrans (Logic.eq_sym hzx) hza.
have hCNonempty:C !=set0 by exists a; split.
have hRelativeOpen:exists2 V,open V & C=A `&` V.
  exists C; first exact hOpenC.
  apply/seteqP; split.
  - move=>x hx; split; first exact hx.1; exact hx.
  - by move=>x [_ hx].
have hRelativeClosed:exists2 V,closed V & C=A `&` V.
  exists (~` D); first exact:open_closedC hOpenD.
  apply/seteqP; split.
  - move=>x [hx he]; split=>// [[_ hne]]; exact:hne he.
  - move=>x [hx hNot]; split=>//.
    apply:contrapT=>hNe; apply:hNot; by split.
have hWhole:C=A:=hConnected C hCNonempty hRelativeOpen hRelativeClosed.
have hCb:C b by rewrite hWhole.
exact hCb.2.
Qed.
