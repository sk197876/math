(** Federer (1969), 3.4.5, p. 319, referring
    to 1.10.5: finite-dimensional source spaces give
    finite-dimensional scalar derivative spaces. All arguments use
    the abstract multilinear laws and the existing basis theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis TensorFamilyUP TensorFamilyBasis
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
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Variable m:nat.
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(@ContinuousMultilinear.space R m X R^o NX NS hNX hNS).
Local Notation ev:=(@ContinuousMultilinear.evaluation R m X R^o NX NS hNX hNS).
Local Notation ZN:=(@ContinuousMultilinear.norm R m X R^o NX NS hNX hNS).
Local Notation B:=({ffun 'I_m->'I_n}).

(** Source for [finite_multilinear_basis_values_extensional]:
    the finite-coordinate determination of scalar derivative forms
    used in 3.4.5, p. 319, from 1.1.2 and
    1.10.5. All degrees and the zero source space remain. *)
Lemma finite_multilinear_basis_values_extensional (z w:Z):
  (forall l:B,ev [ffun i=>b (l i)] z=ev [ffun i=>b (l i)] w) ->z=w.
Proof.
move=>hBasis.
have hZ:=@ContinuousMultilinear.laws R m X R^o NX NS hNX hNS.
have hZero u:ev u (z-w)=0.
  apply:(@multilinear_basis_induction R m (fun _:'I_m=>X)
    (fun _:'I_m=>Choice.clone 'I_n _) (fun _=>b) (fun _=>hb) R^o
    (fun u=>ev u (z-w)) (continuous_multilinear_evaluation hZ (z-w)) (fun r=>r=0)).
  - reflexivity.
  - by move=>x y -> ->;rewrite addr0.
  - by move=>c x ->;rewrite scaler0.
  - move=>l;change (ev [ffun i=>b (l i)] (z-w)=0).
    by rewrite linearB /= (hBasis l) subrr.
apply:(continuous_multilinear_extensional hZ)=>u.
apply/eqP;rewrite -subr_eq0 -linearB;apply/eqP;exact:hZero.
Qed.

(** Source for [finite_multilinear_coordinate_map]: evaluation
    on all original basis tuples, 3.4.5, p. 319,
    expressed in finite coordinates only to prove finite dimensionality. *)
Definition finite_multilinear_coordinate_map (z:Z):coordinate_space R #|B| :=
  [ffun j:'I_#|B|=>ev [ffun i=>b ((enum_val j) i)] z].

(** Source for [finite_multilinear_coordinate_linear]: basis-tuple
    evaluation is linear in the derivative form, 3.4.5, p. 319. *)
Lemma finite_multilinear_coordinate_linear:linear finite_multilinear_coordinate_map.
Proof.
move=>c z w;apply/ffunP=>j.
by rewrite /finite_multilinear_coordinate_map !ffunE linearP.
Qed.

(** Source for [finite_multilinear_coordinate_hom]: the linear
    coordinate injection used for 3.4.5, p. 319. *)
Definition finite_multilinear_coordinate_hom:Hom Z (coordinate_space R #|B|) :=
  @HomMap R Z (coordinate_space R #|B|) finite_multilinear_coordinate_map
    (introT (asboolP _) finite_multilinear_coordinate_linear).

(** Source for [finite_multilinear_coordinate_injective]: the
    original form is determined by the finite basis values,
    supporting compactness in 3.4.5, p. 319. *)
Lemma finite_multilinear_coordinate_injective:injective finite_multilinear_coordinate_hom.
Proof.
move=>z w hEqual;apply:finite_multilinear_basis_values_extensional=>l.
have hValue:=congr1 (fun v:coordinate_space R #|B|=>v (enum_rank l)) hEqual.
by move:hValue;rewrite /finite_multilinear_coordinate_hom /= /finite_multilinear_coordinate_map
  !ffunE enum_rankK.
Qed.

(** Source for [finite_scalar_multilinear_basis_exists]: a
    finite-dimensional X has a finite-dimensional scalar m-linear
    form space, as used in 3.4.5, p. 319.
    The finite independent-family bound of 1.6.1 gives an
    actual basis; none is assumed or chosen globally. *)
Theorem finite_scalar_multilinear_basis_exists:
  exists q (e:'I_q->Z),is_basis e /\(q<=#|B|)%N.
Proof.
apply:bounded_independent_basis=>q e he.
have hIndependent:=@finite_independent_map R (Finite.clone 'I_q _) Z
  (coordinate_space R #|B|) (hom_as_linear finite_multilinear_coordinate_hom) e
  finite_multilinear_coordinate_injective he.
have hDimension:=@finite_independent_dimension R
  (finite_basis_vect (@coordinate_basisP R #|B|)) q
  (fun i=>finite_multilinear_coordinate_hom (e i)) hIndependent.
by rewrite finite_basis_dimension card_ord in hDimension.
Qed.
End Coordinates.
