(** Federer (1969), 3.4.8(6), pp. 328–329:
    the actual H_p acts transitively on the unit
    sphere perpendicular to its fixed tail. Frame
    extension supplies the original orthogonal group element. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  OrthonormalFamilies OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  PointwiseFixingLocusUP PointwiseFixingLocusSealed OrthogonalCoordinateFixing
  OrdinalCoordinateTail OrthogonalFrameFixingTransitivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_prefix_fixing_transitive]: H_p
    acts transitively on the original prefix sphere,
    3.4.8(6), pp. 328–329. Every fixed tail vector
    remains pointwise fixed. *)
Theorem orthogonal_prefix_fixing_transitive (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (hON:orthonormal_family B e) p (hPN:(p<=n)%N) (u v:X):
  B u u = 1 ->B v v = 1 ->
  (forall i:'I_n,(p<=i)%N ->B u (e i) = 0) ->
  (forall i:'I_n,(p<=i)%N ->B v (e i) = 0) ->
  exists g:@orthogonal_group R X B hB n e he,
    @analytic_prefix_rotation_group R X B hB n e he p g /\orthogonal_element_map g u = v.
Proof.
move=>hU hV hUF hVF.
pose tail:=fun i:'I_(n-p)=>e (ordinal_coordinate_tail_index hPN i).
have hTail:orthonormal_family B tail.
  move=>i j;rewrite /tail hON.
  by rewrite (inj_eq (@ordinal_coordinate_tail_injective n p hPN)).
have hTailU i:B u (tail i) = 0.
  apply:hUF;rewrite ordinal_coordinate_tail_value;exact:leq_addr.
have hTailV i:B v (tail i) = 0.
  apply:hVF;rewrite ordinal_coordinate_tail_value;exact:leq_addr.
have [f [hF [hFU hFFixed]]]:=@orthogonal_frame_fixing_transitive R X B hB n e he
  (n-p) tail hTail u v hU hV hTailU hTailV.
pose g:=@orthogonal_element_of R X B hB n e he f hF.
exists g;split;last by rewrite /g orthogonal_element_ofE.
apply/(@orthogonal_coordinate_fixing_membership R X B hB n e he [set i:'I_n|(p<=i)%N] g).
move=>i hi;have [j hJ]:=@ordinal_coordinate_tail_complete n p hPN i hi.
rewrite /g orthogonal_element_ofE -hJ;exact:hFFixed.
Qed.
