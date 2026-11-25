(** Federer (1969), 1.6.6, p. 27: a nonzero simple real m-vector is complex
    exactly when m=2p and it is a nonzero real multiple of v_1 wedge i v_1
    wedge ... wedge v_p wedge i v_p. The definition is the abstract
    condition on its associated space; the paired product is proved to
    represent every such vector. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleDimensionCriterion SimpleProportionality
  SubspaceCarrier SubspaceBasisProduct ComplexScalarSealed ComplexCharacteristic
  ScalarRestriction ComplexSubspaces ComplexFiniteSubspace ComplexPairedVectors
  ComplexPairedPlanes FiniteIndependence FiniteBasisComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ComplexSimple.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation hR := (real_two_nonzero R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).

(** Source for [complex_simple_vector]: Federer 1.6.6,
    p. 27, definition of a complex nonzero simple m-vector. The
    associated real subspace must be a complex subspace. *)
Definition complex_simple_vector m (xi : exterior_power VR m) :=
  xi != 0 /\ simple xi /\ complex_stable_subspace (FedererSimple.T xi).

(** Source for [complex_simple_representation]: Federer
    1.6.6, p. 27, forward implication in the paired representation.
    A complex basis of the finite associated subspace supplies the
    factors. The nonzero scalar is obtained from equality of associated
    spaces. No finite-dimensional hypothesis on V is imposed. *)
Theorem complex_simple_representation m (xi : exterior_power VR m) :
  complex_simple_vector xi ->
  exists p, exists v : 'I_p -> V, exists r : R,
    m = (p+p)%N /\ r != 0 /\
    component_val xi = r *: component_val (paired_complex_vector v).
Proof.
move=> [hxi [sxi hS]].
have [b [hb hxb]] := @simple_is_basis_product R hR VR m xi hxi sxi.
have [p [v hv]] := complex_subspace_basis_exists hS hb.
have hm := @complex_subspace_even_dimension R V (FedererSimple.T xi) hS m b hb p v hv.
subst m.
pose w j := subspace_val (v j).
have hw : finite_independent w.
  exact: (finite_independent_map (@subspace_val_injective C V (stable_complex_subspace hS))
    (finite_basis_independent hv)).
have hpair : paired_complex_vector w != 0 := independent_paired_vector_nonzero hw.
have heq z : FedererSimple.T xi z <-> FedererSimple.T (paired_complex_vector w) z.
  rewrite (paired_vector_complex_span hpair).
  exact: iff_sym (subspace_basis_span hv z).
have [r [hr hx]] := (proj1 (@simple_associated_equal R hR VR (p+p) xi
  (paired_complex_vector w) hxi hpair (paired_complex_vector_simple w))) heq.
exists p, w, r; split=> //; split=> //.
by rewrite hx linearZ.
Qed.

(** Source for [paired_representation_complex]: Federer
    1.6.6, p. 27, reverse implication in the paired representation.
    For a nonzero simple vector, the displayed representation makes
    its associated real subspace complex. *)
Theorem paired_representation_complex m (xi : exterior_power VR m)
  (hxi : xi != 0) (sxi : simple xi) p (v : 'I_p -> V) r :
  m = (p+p)%N -> r != 0 ->
  component_val xi = r *: component_val (paired_complex_vector v) -> complex_simple_vector xi.
Proof.
move=> hm hr hx; subst m.
have h : xi = r *: paired_complex_vector v.
  apply: val_inj; by rewrite linearZ.
have hp : paired_complex_vector v != 0.
  by move: hxi; rewrite h scaler_eq0 (negbTE hr) /=.
split=> //; split=> //.
move=> z hz; rewrite h in hz *.
apply: (proj2 (@associated_scale_nonzero R VR (p+p) (paired_complex_vector v) r hr _)).
apply: (paired_vector_complex hp).
exact: (proj1 (@associated_scale_nonzero R VR (p+p) (paired_complex_vector v) r hr z) hz).
Qed.

(** Source for [complex_simple_iff_paired]: Federer 1.6.6,
    p. 27, complete characterisation. The pair count p is half the
    real degree, and the scalar is necessarily nonzero. Degree zero
    uses the literal empty product, so a simple zero-vector is the unit. *)
Theorem complex_simple_iff_paired m (xi : exterior_power VR m)
  (hxi : xi != 0) (sxi : simple xi) :
  complex_simple_vector xi <->
  exists p, exists v : 'I_p -> V, exists r : R,
    m = (p+p)%N /\ r != 0 /\
    component_val xi = r *: @exterior_word R VR
      (flatten [seq [:: v j; ii *: v j] | j <- enum 'I_p]).
Proof.
split.
- move/complex_simple_representation=> [p [v [r [hm [hr hx]]]]].
  exists p, v, r; split=> //; split=> //.
  by rewrite -paired_complex_vector_word.
- move=> [p [v [r [hm [hr hx]]]]].
  apply: (paired_representation_complex hxi sxi hm hr).
  rewrite paired_complex_vector_word; exact hx.
Qed.
End ComplexSimple.
