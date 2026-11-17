(** Federer (1969), 3.4.12, p. 339: the original unitary
    group acts transitively on its Hermitian unit sphere.
    Place the proved complex isometry in the existing real
    orthogonal group and verify its original scalar-commutation law.
    Common orthogonal directions remain fixed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed HermitianUP HermitianRealImaginary
  InnerNorm LinearBasis OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  HolomorphicLinear UnitaryGroup HermitianUnitDirectionMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [unitary_sphere_fixing_transitive]: actual unitary
    alignment with fixed common orthogonal directions, supporting the
    original prefix and suffix Haar arguments, 3.4.12, p. 339. *)
Theorem unitary_sphere_fixing_transitive (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) N
    (e:'I_N->restricted_space (ComplexScalars.embed R) X) (he:is_basis e) v w:
  inner_norm (hermitian_real_inner_product hH) v = 1 ->
  inner_norm (hermitian_real_inner_product hH) w = 1 ->
  exists g:@unitary_group R X H hH N e he,
    @orthogonal_element_map R (restricted_space (ComplexScalars.embed R) X)
      (hermitian_real_part H) (hermitian_real_inner_product hH) N e he (set_val g) v=w /\
    forall x,H v x=0 ->H w x=0 ->
      @orthogonal_element_map R (restricted_space (ComplexScalars.embed R) X)
        (hermitian_real_part H) (hermitian_real_inner_product hH) N e he (set_val g) x=x.
Proof.
move=>hv hw.
have [L [hL [hIsometry hFix]]]:=@hermitian_unit_direction_fixing_isometry_exists R X H hH v w hv hw.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose B:=hermitian_real_part H;pose hB:=hermitian_real_inner_product hH.
pose realL:=complex_hom_real L.
have hOrthogonal:is_orthogonal_map B B (hom_as_linear realL).
  move=>x y;change (ComplexScalars.re (H (L x) (L y))=ComplexScalars.re (H x y)).
  by rewrite hIsometry.
pose g:=@orthogonal_element_of R XR B hB N e he (hom_as_linear realL) hOrthogonal.
have hMember:@unitary_group R X H hH N e he g.
  apply/(@unitary_group_membership R X H hH N e he g)=>c x.
  rewrite /g !orthogonal_element_ofE !hom_as_linearE !complex_hom_real_values.
  by rewrite linearZ.
pose u:@unitary_group R X H hH N e he:=exist _ g (mem_set hMember).
exists u;split.
- change (L v=w).
  exact:hL.
- move=>x hxv hxw;change (L x=x).
  exact:hFix x hxv hxw.
Qed.
