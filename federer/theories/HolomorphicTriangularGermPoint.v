(** Federer (1969), 3.4.12, p. 339, extending the
    zero-dimensional case of 3.4.8(11), p. 333:
    actual triangular monic representatives vanishing on a germ
    give containment in the point germ. Their common zero
    neighbourhood is supplied by the original vanishing-ideal laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis FiniteCoordinates ScalarRestriction ComplexScalarSealed
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing SetGermUP SetGermSealed SetGermLaws SetGermOrder
  HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative FieldPrefixCoordinatesUP FieldTriangularMonicZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_triangular_germ_point]: the simultaneous
    prepared equations isolate the zero-depth common variety germ,
    3.4.8(11), p. 333, under 3.4.12, p. 339.
    Only the proved field-level triangular inference is new. *)
Theorem holomorphic_triangular_germ_point (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX)
    n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X (ComplexScalars.C R)^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (hJN:forall j:'I_n,(j<=n)%N) (P:forall j:'I_n,Hom X (coordinate_space (ComplexScalars.C R) j))
    (k:'I_n->nat) (b:forall j:'I_n,'I_(k j)->coordinate_space (ComplexScalars.C R) j->ComplexScalars.C R)
    (f:'I_n->@holomorphic_representative_type R X NX hNX 0)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) 0):
  (forall j,is_field_prefix_projection omega (hJN j) (P j)) ->
  (forall j,(0<k j)%N) ->(forall j i,b j i 0 = 0) ->
  (forall j x,holomorphic_representative_value (f j) x = (omega j x)^+(k j)+
    \sum_(i<k j) b j i (P j x)*(omega j x)^+(i:nat)) ->
  (forall j,@HolomorphicSetIdeal.value R X NX hNX 0 sigma (holomorphic_germ (f j))) ->
  set_germ_subset sigma (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 [set 0]).
Proof.
move=>hP hPositive hCentre hValues hVanish.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [S hS]:=@set_germ_has_representative T 0 sigma.
have hEach j:nbhs (0:T) [set x|S x ->holomorphic_representative_value (f j) x = 0].
  have hMembership:=hVanish j;rewrite -hS in hMembership.
  have [U [hU [hU0 hZero]]]:=(@holomorphic_set_ideal_representative_equation R X NX hNX 0 (f j) S).1 hMembership.
  have hNear:nbhs (0:T) U by rewrite openE in hU;exact:hU 0 hU0.
  exact:(filterS (fun x hx hSx=>hZero x hSx hx) hNear).
have hCommon:=@filter_forall T 'I_n (fun j x=>S x ->holomorphic_representative_value (f j) x = 0)
  (nbhs (0:T)) (nbhs_filter (0:T)) hEach.
have hPoint:nbhs (0:T) [set x|S x ->x = 0].
  apply:(filterS _ hCommon)=>x hEq hSx.
  apply:(@field_triangular_monic_zero (ComplexScalars.C R) X n e he omega hDual hJN P k b hP hPositive hCentre x).
  move=>j;rewrite -(hValues j x);exact:hEq j hSx.
rewrite -hS;apply/set_germ_subset_original.
rewrite nbhsE in hPoint.
have [U [hU hU0] hSub]:=hPoint.
exists U;split;first exact:hU.
split;first exact:hU0.
move=>x hSx hUx;exact:hSub x hUx hSx.
Qed.
