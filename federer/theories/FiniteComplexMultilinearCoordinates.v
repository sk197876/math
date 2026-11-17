(** Federer (1969), 3.4.12, p. 339, extending the coefficient
    compactness argument of 3.4.5, p. 319: finite-dimensional
    source spaces give finite-dimensional complex-valued real derivative
    spaces. Reuse basis-tuple determination and the existing independent
    family bound; add only the actual two scalar coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarUP ComplexScalarSealed ComplexScalarLaws
  ComplexModulus ComplexScalarNorm LinearBasis TensorFamilyUP TensorFamilyBasis
  ContinuousMultilinearUP ContinuousMultilinearSealed FiniteCoordinates FiniteIndependence
  FiniteBasisComparison FiniteDimension IndependentMap BoundedIndependentBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable n:nat.
Variable b:'I_n->X.
Variable hb:is_basis b.
Variable m:nat.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(@ContinuousMultilinear.space R m X CR NX N hNX hN).
Local Notation ev:=(@ContinuousMultilinear.evaluation R m X CR NX N hNX hN).
Local Notation B:=({ffun 'I_m->'I_n}).
Local Notation I:=([the finType of (B*bool)%type]).

(** Source for [finite_complex_multilinear_basis_values_extensional]:
    the original basis tuples determine each complex-valued derivative,
    extending 3.4.5, p. 319. Degree zero and the zero
    source dimension remain. *)
Lemma finite_complex_multilinear_basis_values_extensional (z w:Z):
  (forall l:B,ev [ffun i=>b (l i)] z=ev [ffun i=>b (l i)] w) ->z=w.
Proof.
move=>hBasis.
have hZ:=@ContinuousMultilinear.laws R m X CR NX N hNX hN.
have hZero u:ev u (z-w)=0.
  apply:(@multilinear_basis_induction R m (fun _:'I_m=>X)
    (fun _:'I_m=>Choice.clone 'I_n _) (fun _=>b) (fun _=>hb) CR
    (fun u=>ev u (z-w)) (continuous_multilinear_evaluation hZ (z-w)) (fun r=>r=0)).
  - reflexivity.
  - by move=>x y -> ->;rewrite addr0.
  - by move=>c x ->;rewrite scaler0.
  - move=>l;change (ev [ffun i=>b (l i)] (z-w)=0).
    by rewrite linearB /= (hBasis l) subrr.
apply:(continuous_multilinear_extensional hZ)=>u.
apply/eqP;rewrite -subr_eq0 -linearB;apply/eqP;exact:hZero.
Qed.

(** Source for [finite_complex_multilinear_coordinate_map]: actual real
    and imaginary basis-tuple values give a finite real coordinate
    map for the derivative space, extending 3.4.5, p. 319. *)
Definition finite_complex_multilinear_coordinate_map (z:Z):coordinate_space R #|I| :=
  [ffun j:'I_#|I|=>if (enum_val j).2 then ComplexScalars.im (ev [ffun i=>b ((enum_val j).1 i)] z)
    else ComplexScalars.re (ev [ffun i=>b ((enum_val j).1 i)] z)].

(** Source for [finite_complex_multilinear_coordinate_linear]: every
    original coordinate is real linear in the derivative form,
    supporting the finite coefficient argument of 3.4.5, p. 319. *)
Lemma finite_complex_multilinear_coordinate_linear:linear finite_complex_multilinear_coordinate_map.
Proof.
move=>c z w;apply/ffunP=>j.
rewrite /finite_complex_multilinear_coordinate_map !ffunE.
case hCase:(enum_val j).2;rewrite linearP.
- change (ComplexScalars.im (ComplexScalars.embed R c*ev [ffun i=>b ((enum_val j).1 i)] z+
      ev [ffun i=>b ((enum_val j).1 i)] w)=c*ComplexScalars.im (ev [ffun i=>b ((enum_val j).1 i)] z)+
      ComplexScalars.im (ev [ffun i=>b ((enum_val j).1 i)] w)).
  by rewrite (complex_im_add (ComplexScalars.laws R)) (complex_im_scale (ComplexScalars.laws R)).
- change (ComplexScalars.re (ComplexScalars.embed R c*ev [ffun i=>b ((enum_val j).1 i)] z+
      ev [ffun i=>b ((enum_val j).1 i)] w)=c*ComplexScalars.re (ev [ffun i=>b ((enum_val j).1 i)] z)+
      ComplexScalars.re (ev [ffun i=>b ((enum_val j).1 i)] w)).
  by rewrite (complex_re_add (ComplexScalars.laws R)) (complex_re_scale (ComplexScalars.laws R)).
Qed.

(** Source for [finite_complex_multilinear_coordinate_hom]: the finite
    real coordinate map as an actual linear map, extending
    the coefficient compactness argument of 3.4.5, p. 319. *)
Definition finite_complex_multilinear_coordinate_hom:Hom Z (coordinate_space R #|I|):=
  @HomMap R Z (coordinate_space R #|I|) finite_complex_multilinear_coordinate_map
    (introT (asboolP _) finite_complex_multilinear_coordinate_linear).

(** Source for [finite_complex_multilinear_coordinate_injective]: the
    two original scalar coordinates detect equality of derivatives,
    extending 3.4.5, p. 319. *)
Lemma finite_complex_multilinear_coordinate_injective:injective finite_complex_multilinear_coordinate_hom.
Proof.
move=>z w hEqual;apply:finite_complex_multilinear_basis_values_extensional=>l.
apply:ComplexScalarTheory.coordinates_injective.
- have h:=congr1 (fun v:coordinate_space R #|I|=>v (enum_rank (l,false))) hEqual.
  by move:h;rewrite /finite_complex_multilinear_coordinate_hom /= /finite_complex_multilinear_coordinate_map
    !ffunE enum_rankK /=.
- have h:=congr1 (fun v:coordinate_space R #|I|=>v (enum_rank (l,true))) hEqual.
  by move:h;rewrite /finite_complex_multilinear_coordinate_hom /= /finite_complex_multilinear_coordinate_map
    !ffunE enum_rankK /=.
Qed.

(** Source for [finite_complex_multilinear_basis_exists]: finite real
    dimension of the actual complex-valued derivative space, extending
    3.4.5, p. 319. The bound includes both scalar coordinates. *)
Theorem finite_complex_multilinear_basis_exists:
  exists q (e:'I_q->Z),is_basis e /\(q<=#|I|)%N.
Proof.
apply:bounded_independent_basis=>q e he.
have hIndependent:=@finite_independent_map R (Finite.clone 'I_q _) Z
  (coordinate_space R #|I|) (hom_as_linear finite_complex_multilinear_coordinate_hom) e
  finite_complex_multilinear_coordinate_injective he.
have hDimension:=@finite_independent_dimension R
  (finite_basis_vect (@coordinate_basisP R #|I|)) q
  (fun i=>finite_complex_multilinear_coordinate_hom (e i)) hIndependent.
by rewrite finite_basis_dimension card_ord in hDimension.
Qed.
End Coordinates.
