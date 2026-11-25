(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    pp. 328–329: the original complex prefix sphere is the
    exact isometric image of the real unit sphere of dimension
    2p. Use the original prefix maps and paired scalar coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexNormUP HermitianUP
  HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  OrthonormalFamilies FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct HolomorphicLinear
  HolomorphicCoordinateNorm StandardHermitianCoordinates ComplexEuclideanCoordinates FieldPrefixCoordinatesUP
  FieldPrefixCoordinateLaws FieldPrefixFixedSupport HermitianBasisCoordinates HolomorphicPrefixSectionIsometry
  UnitaryFixingSphereAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coordinates.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family H e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Variable p:nat.
Variable hPN:(p<=n)%N.
Local Notation C:=(ComplexScalars.C R).
Local Notation Y:=(coordinate_space C p).
Local Notation YR:=(R_n R (p+p)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation XT:=(inner_metric_space hB).
Local Notation YT:=(inner_metric_space (@euclidean_inner_productP R (p+p))).
Local Notation NY:=(@holomorphic_coordinate_norm R p).
Variable P:Hom X Y.
Variable S:Hom Y X.
Variable hP:is_field_prefix_projection omega hPN P.
Variable hS:is_field_prefix_section e hPN S.
Local Notation V:=(@unitary_fixing_sphere R X H hH n e [set i:'I_n|(p<=i)%N]).

(** Source for [holomorphic_prefix_section_tail_perpendicular]: the
    actual complex prefix is perpendicular to every omitted original
    coordinate vector, 3.4.12, p. 339. *)
Lemma holomorphic_prefix_section_tail_perpendicular y (i:'I_n):
  (p<=i)%N ->H (S y) (e i)=0.
Proof.
move=>hPI.
rewrite (@hermitian_conjugate_symmetric R X H hH (e i) (S y))
  (@hermitian_basis_coordinate R X H hH n e he hON omega hDual i (S y))
  (@field_prefix_section_tail_zero C X n e omega hDual p hPN S hS i hPI y).
by rewrite -(rmorph0 (ComplexScalars.embed R)) conjugate_real.
Qed.

(** Source for [holomorphic_prefix_section_projection_fixed]: every
    actual vector perpendicular to the fixed tail is recovered from
    its original prefix coordinates, 3.4.12, p. 339. *)
Lemma holomorphic_prefix_section_projection_fixed x:
  (forall i:'I_n,(p<=i)%N ->H x (e i)=0) ->S (P x)=x.
Proof.
move=>hTail;apply:(@field_prefix_projection_fixed_support C X n e he omega hDual p hPN P S hP hS x)=>i hi.
exact:(@hermitian_orthogonal_coordinate_zero R X H hH n e he hON omega hDual i x (hTail i hi)).
Qed.

(** Source for [holomorphic_prefix_complex_sphere_image]: the exact
    original prefix inclusion maps its complex unit sphere onto the
    actual fixed-tail sphere, 3.4.12, p. 339. *)
Lemma holomorphic_prefix_complex_sphere_image:
  S @` [set y:Y|NY y= 1]=V.
Proof.
apply/seteqP;split=>x.
- move=>[y hy <-];split.
  + by rewrite (@holomorphic_prefix_section_norm R X H hH n e hON p hPN S hS y).
  + move=>i hi;exact:holomorphic_prefix_section_tail_perpendicular.
- move=>[hUnit hTail];exists (P x).
  + change (NY (P x)= 1).
    rewrite -(@holomorphic_prefix_section_norm R X H hH n e hON p hPN S hS (P x))
      (holomorphic_prefix_section_projection_fixed hTail);exact:hUnit.
  + exact:holomorphic_prefix_section_projection_fixed.
Qed.

(** Source for [holomorphic_prefix_real_sphere_inclusion]: the
    original prefix inclusion after the original real-to-complex
    coordinate identification, 3.4.12, p. 339. *)
Definition holomorphic_prefix_real_sphere_inclusion:Hom YR XR:=
  hom_comp (complex_hom_real S) (@complex_from_real_coordinate_hom R p).

(** Source for [holomorphic_prefix_real_sphere_projection]: the
    original complex prefix followed by its exact real coordinate
    map, 3.4.12, p. 339. *)
Definition holomorphic_prefix_real_sphere_projection:Hom XR YR:=
  hom_comp (@complex_real_coordinate_hom R p) (complex_hom_real P).
Local Notation SR:=holomorphic_prefix_real_sphere_inclusion.
Local Notation PR:=holomorphic_prefix_real_sphere_projection.

(** Source for [holomorphic_prefix_real_sphere_section]: the actual
    real coordinate maps retain the exact section identity,
    3.4.12, p. 339. *)
Lemma holomorphic_prefix_real_sphere_section:cancel SR PR.
Proof.
move=>y;change (complex_real_coordinates (P (S (complex_from_real_coordinates y)))=y).
rewrite (@field_prefix_projection_section C X n e omega p hPN P S hDual hP hS).
exact:complex_from_real_coordinatesK.
Qed.

(** Source for [holomorphic_prefix_real_sphere_norm]: the actual
    inclusion retains the exact real Euclidean norm in degree 2p,
    3.4.12, p. 339. *)
Lemma holomorphic_prefix_real_sphere_norm y:
  inner_norm hB (SR y)=inner_norm (@euclidean_inner_productP R (p+p)) y.
Proof.
change (inner_norm hB (S (complex_from_real_coordinates y))=
  inner_norm (@euclidean_inner_productP R (p+p)) y).
rewrite (@holomorphic_prefix_section_norm R X H hH n e hON p hPN S hS).
exact:complex_inverse_euclidean_coordinate_norm.
Qed.

(** Source for [holomorphic_prefix_real_sphere_distance]: the
    original chart is isometric for the original ambient metrics,
    3.4.12, p. 339. *)
Lemma holomorphic_prefix_real_sphere_distance (x y:YT):
  mdist (SR x:XT) (SR y:XT)=mdist x y.
Proof.
rewrite !inner_metric_distanceE.
have hNorm:=holomorphic_prefix_real_sphere_norm (x-y).
rewrite linearB /= in hNorm;exact:hNorm.
Qed.

(** Source for [holomorphic_prefix_real_sphere_image]: the original
    prefix sphere equals the actual isometric image of the unit
    sphere in R^(2p), 3.4.12, p. 339. *)
Lemma holomorphic_prefix_real_sphere_image:
  SR @` [set y:YT|inner_norm (@euclidean_inner_productP R (p+p)) y= 1]=V.
Proof.
rewrite -holomorphic_prefix_complex_sphere_image.
apply/seteqP;split=>x.
- move=>[y hy <-];exists (complex_from_real_coordinates y);last by [].
  change (NY (complex_from_real_coordinates y)= 1).
  by rewrite complex_inverse_euclidean_coordinate_norm.
- move=>[y hy <-];exists (complex_real_coordinates y).
  + change (inner_norm (@euclidean_inner_productP R (p+p)) (complex_real_coordinates y)= 1).
    by rewrite -complex_euclidean_coordinate_norm.
  + change (S (complex_from_real_coordinates (complex_real_coordinates y))=S y).
    by rewrite complex_real_coordinatesK.
Qed.
End Coordinates.
