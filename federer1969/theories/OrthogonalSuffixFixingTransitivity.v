(** Federer (1969), 3.4.8(8), p. 329:
    the original Q_m acts transitively
    on the unit sphere perpendicular to
    the original first m basis vectors.
    Apply the existing fixed-frame extension theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthonormalFamilies OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  OrthogonalCoordinateFixing OrthogonalFrameFixingTransitivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [orthogonal_suffix_fixing_transitive]: the
    original sphere transitivity of Q_m in
    3.4.8(8), p. 329. Every original
    fixed prefix vector remains fixed;
    the actual orthogonal map is obtained
    from the proved frame extension. *)
Theorem orthogonal_suffix_fixing_transitive (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (hON:orthonormal_family B e) m (hMN:(m<=n)%N) (u v:X):
  B u u = 1 ->B v v = 1 ->
  (forall i:'I_n,(i<m)%N ->B u (e i) = 0) ->
  (forall i:'I_n,(i<m)%N ->B v (e i) = 0) ->
  exists q:@orthogonal_group R X B hB n e he,
    @analytic_suffix_rotation_group R X B hB n e he m q /\orthogonal_element_map q u = v.
Proof.
move=>hU hV hUF hVF.
pose frame:=fun i:'I_m=>e (widen_ord hMN i).
have hFrame:orthonormal_family B frame.
  move=>i j;rewrite /frame hON;by rewrite -!val_eqE /=.
have hFrameU i:B u (frame i) = 0:=hUF (widen_ord hMN i) (ltn_ord i).
have hFrameV i:B v (frame i) = 0:=hVF (widen_ord hMN i) (ltn_ord i).
have [f [hF [hFU hFixed]]]:=@orthogonal_frame_fixing_transitive R X B hB n e he
  m frame hFrame u v hU hV hFrameU hFrameV.
pose q:=@orthogonal_element_of R X B hB n e he f hF.
exists q;split;last by rewrite /q orthogonal_element_ofE.
apply/(@orthogonal_coordinate_fixing_membership R X B hB n e he [set i:'I_n|(i<m)%N] q).
move=>i hI;pose a:'I_m:=Ordinal hI.
have hIndex:widen_ord hMN a = i by apply:val_inj.
rewrite /q orthogonal_element_ofE -hIndex;exact:hFixed.
Qed.
