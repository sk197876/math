(** Federer (1969), 3.2.26(3), p. 262: partition the
    source into Borel pieces on which the orientation varies by
    at most delta. State exact graph and partition laws first;
    auxiliary defaults do not supply any missing orientation values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP
  PartialFunctionPreimages BorelPartialTotalExtension BorelFunctionBasic TopologicalBorel
  BorelFamilyBasic SmallBorelPartitionUP SmallBorelPartitionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_borel_partial_small_partition]: the Borel
    partition H and the chosen orientation vector for each
    nonempty member, Federer 3.2.26(3), p. 262.
    The union is exactly W intersect the actual domain of T.
    Every nonempty piece chooses an actual value of T on
    that same piece; no range property is required of an
    unused centre on an empty piece. *)
Definition is_borel_partial_small_partition (R:realType) (X:topologicalType)
    (Y:metricType R) (W:set X) (T:partial_function X Y) (e:R)
    (P:nat->set X) (c:nat->Y):=
  (forall i,borel_set (P i)) /\
  (forall i j,i!=j ->forall x,P i x ->P j x ->False) /\
  (\bigcup_i P i)=W `&` partial_function_domain T /\
  (forall i,P i !=set0 ->exists x,P i x /\partial_function_graph T x (c i)) /\
  forall i x y,P i x ->partial_function_graph T x y ->mdist y (c i)<=e.

(** Source for [borel_partial_small_partition_exists]: the
    partition choice in Federer 3.2.26(3), p. 262,
    expanded using the small Borel partitions of 2.3.5,
    p. 76. The existing opaque total extension preserves
    every defined graph value. Its auxiliary default is used
    only to form Borel preimages, subsequently intersected with
    the original partial domain. Empty pieces are retained. *)
Theorem borel_partial_small_partition_exists (R:realType) (X:topologicalType)
    (Y:metricType R) (W:set X) (T:partial_function X Y) (e:R) (y0:Y):
  (exists D:set Y,countable D /\dense D) ->borel_set W ->0<e ->
  (forall U:set Y,open U ->borel_set (partial_function_preimage T U)) ->
  exists (P:nat->set X) (c:nat->Y),is_borel_partial_small_partition W T e P c.
Proof.
move=>[D [hD hDense]] hW he hBorel.
have [J [hJ [_ hJBorel]]]:=borel_partial_total_extension_exists y0 hBorel.
have hDomain:borel_set (partial_function_domain T).
  have h:=hBorel setT openT; by rewrite partial_function_preimage_whole in h.
pose B:=@SmallBorelPartition.value R Y D e hD hDense he.
have hB:=@SmallBorelPartition.laws R Y D e hD hDense he.
pose P i:=W `&` partial_function_domain T `&` (J @^-1` B i).
have hPBorel i:borel_set (P i).
  have hPre:=@borel_function_preimage X (Topological.clone Y _) J hJBorel
    (B i) (small_partition_borel hB i).
  exact (@borel_family_binary_intersection X setT (@borel_set X)
    (borel_sets_family X) (W `&` partial_function_domain T) (J @^-1` B i)
    (borel_family_binary_intersection (borel_sets_family X) hW hDomain) hPre).
have hCentre i:exists c:Y,
    (P i !=set0 ->exists x,P i x /\partial_function_graph T x c) /\
    forall x y,P i x ->partial_function_graph T x y ->mdist y c<=e.
  have [hNonempty|hEmpty]:=pselect (P i !=set0).
  - have [a ha]:=hNonempty; have [b hb]:=ha.1.2.
    have hJb:J a=b:=hJ a b hb.
    exists b; split; first by move=>_; exists a.
    move=>x y hx hxy.
    have hJy:J x=y:=hJ x y hxy.
    have hy:B i y by rewrite -hJy; exact hx.2.
    have hbB:B i b by rewrite -hJb; exact ha.2.
    exact:(@small_partition_diameter R Y e B hB i y b hy hbB).
  - exists y0; split.
    + by move=>h; exfalso; exact:hEmpty h.
    + move=>x y hx _; exfalso; apply:hEmpty; by exists x.
have [c hc]:=choice hCentre.
exists P,c; split; first exact hPBorel; split.
- move=>i j hij x hix hjx.
  exact:(@small_partition_disjoint R Y e B hB i j hij (J x) hix.2 hjx.2).
- split.
  + apply/seteqP; split=>x.
    * by move=>[i _ hx]; exact hx.1.
    * move=>hx.
      have hAll:(\bigcup_i B i) (J x) by rewrite (small_partition_cover hB).
      have [i _ hi]:=hAll; exists i; first exact I.
      by split.
  + split; first by move=>i; exact:(hc i).1.
    move=>i; exact:(hc i).2.
Qed.
