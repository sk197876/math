(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    pp. 329–330: the original suffix sphere has the exact
    paired real chart of dimension twice its complex dimension.
    Reorder the original basis and apply the proved prefix chart. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexNormUP HermitianUP
  HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  OrthonormalFamilies FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct HolomorphicLinear
  HolomorphicCoordinateNorm StandardHermitianCoordinates ComplexEuclideanCoordinates FieldPrefixCoordinatesUP
  FieldPrefixCoordinatesSealed FieldPrefixCoordinateLaws HolomorphicPrefixSphereCoordinates UnitaryFixingSphereAction
  OrdinalCoordinateTail OrdinalSuffixReordering.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_suffix_sphere_coordinate_witnesses]: the
    original suffix projection, exact isometry, section identity and
    sphere image, with no measure or chart conclusion assumed,
    3.4.12, p. 339. *)
Theorem holomorphic_suffix_sphere_coordinate_witnesses (R:realType) (X:lmodType (ComplexScalars.C R))
  (H:X->X->ComplexScalars.C R) (hH:is_hermitian_product H)
  n (e:'I_n->X) (he:is_basis e) (hON:orthonormal_family H e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (hDual:forall i j,omega i (e j)=if i==j then 1 else 0)
  m (hMN:(m<=n)%N):
  let k:=(n-m)%N in
  let XR:=restricted_space (ComplexScalars.embed R) X in
  let XT:=inner_metric_space (hermitian_real_inner_product hH) in
  let YT:=inner_metric_space (@euclidean_inner_productP R (k+k)) in
  exists (S:Hom (R_n R (k+k)) XR) (P:Hom XR (R_n R (k+k))),
    cancel S P /\
    (forall x y:YT,mdist (S x:XT) (S y:XT)=mdist x y) /\
    S @` [set y:YT|inner_norm (@euclidean_inner_productP R (k+k)) y= 1]=
      @unitary_fixing_sphere R X H hH n e [set i:'I_n|(i<m)%N] /\
    forall x,complex_from_real_coordinates (P x)=
      [ffun i=>omega (ordinal_coordinate_tail_index hMN i) x].
Proof.
move=>k XR XT YT.
have [forward [back [hFB [hBF [hTail hHead]]]]]:=ordinal_suffix_reordering_exists hMN.
pose f:=fun i:'I_(k+m)=>e (forward i).
pose covector:=fun i:'I_(k+m)=>omega (forward i).
have hF:is_basis f:=@basis_reindex (ComplexScalars.C R) (Choice.clone 'I_n _) (Choice.clone 'I_(k+m) _)
  X e he back forward hBF hFB.
have hONF:orthonormal_family H f.
  move=>i j;by rewrite /f hON (inj_eq (can_inj hFB)).
have hDualF i j:covector i (f j)=if i==j then 1 else 0.
  by rewrite /covector /f hDual (inj_eq (can_inj hFB)).
pose hK:=(leq_addr m k).
pose PC:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) X (k+m)%N covector k hK.
pose SC:=@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) X (k+m)%N f k hK.
have hPC:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X (k+m)%N covector k hK.
have hSC:=@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) X (k+m)%N f k hK.
pose S:=@holomorphic_prefix_real_sphere_inclusion R X k SC.
pose P:=@holomorphic_prefix_real_sphere_projection R X k PC.
have hSphere:(@unitary_fixing_sphere R X H hH n e [set i:'I_n|(i<m)%N])=
    (@unitary_fixing_sphere R X H hH (k+m)%N f [set i:'I_(k+m)|(k<=i)%N]).
  apply:funext=>x;apply:propext;split.
  - move=>[hUnit hOrthogonal];split;first exact:hUnit.
    move=>j hJ;case:(split_ordP j) hJ=>[i ->|i ->] hJ.
    + have hSmall:(i<k)%N:=ltn_ord i.
      have hFalse:=leq_ltn_trans hJ hSmall;by rewrite ltnn in hFalse.
    + rewrite /f hHead;exact:(@hOrthogonal (widen_ord hMN i) (ltn_ord i)).
  - move=>[hUnit hOrthogonal];split;first exact:hUnit.
    move=>j hJ;pose i:'I_m:=Ordinal hJ.
    have hIndex:widen_ord hMN i=j by apply:val_inj.
    have hValue:=hOrthogonal (rshift k i) (leq_addr (i:nat) k).
    by rewrite /f hHead hIndex in hValue.
exists S,P;split.
- exact:(@holomorphic_prefix_real_sphere_section R X (k+m)%N f covector hDualF k hK PC SC hPC hSC).
- split.
  + exact:(@holomorphic_prefix_real_sphere_distance R X H hH (k+m)%N f hONF k hK SC hSC).
  + split.
    * rewrite hSphere.
      exact:(@holomorphic_prefix_real_sphere_image R X H hH (k+m)%N f hF hONF covector hDualF k hK PC SC hPC hSC).
    * move=>x;change (complex_from_real_coordinates (P x)) with (complex_from_real_coordinates (complex_real_coordinates (PC x))).
      rewrite complex_real_coordinatesK;apply/ffunP=>i;rewrite hPC /covector ffunE.
      have hIndex:widen_ord hK i=lshift m i by apply:val_inj.
      by rewrite hIndex hTail.
Qed.
