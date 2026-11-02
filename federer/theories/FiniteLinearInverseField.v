(** Federer (1969), 3.1.18, p. 229: an injective differential between
    equal finite dimensions has a bounded linear inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP LinearBasis FiniteIndependence
  FiniteBasisComparison FiniteBasisCriterion FiniteDimension IndependentMap
  RealNormUP NormDifferentialUP NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_injective_linear_inverse_exists]: the equal-
    dimension linear isomorphism used for Dg(a) in 3.1.18, p. 229.
    This is a supporting basis-size argument valid over any field. *)
Lemma finite_injective_linear_inverse_exists (K:fieldType) (X:lmodType K)
    n (b:'I_n->X) (hb:is_basis b) (L:Hom X X) : injective L ->
  exists M:Hom X X, cancel L M /\ cancel M L.
Proof.
move=>hL.
have hi := finite_independent_map hL (finite_basis_independent hb).
have hLb : is_basis (fun i=>L (b i)).
  apply: (@finite_independent_basis K (finite_basis_vect hb) n (fun i=>L (b i))).
  - by rewrite finite_basis_dimension card_ord.
  - exact hi.
have [m [hLm hmL]] := basis_image_inverse_exists hb hLb.
by exists (hom_of_linear m); split.
Qed.

(** Source for [norm_finite_inverse_field_exists]: bounded inverses
    at all nonsingular points of a finite-dimensional differential field,
    supporting the local inverse in 3.1.18, p. 229. Their regularity is
    proved separately; no continuity is assumed of the chosen field. *)
Theorem norm_finite_inverse_field_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (A:X->Prop) (D:X->Hom X X) :
  (forall x, A x -> injective (D x)) ->
  exists E:X->Hom X X, forall x, A x ->
    norm_bounded_linear NX NX (E x) /\ cancel (D x) (E x) /\ cancel (E x) (D x).
Proof.
move=>hinj.
have hex x : exists M:Hom X X, A x ->
    norm_bounded_linear NX NX M /\ cancel (D x) M /\ cancel M (D x).
  case: (pselect (A x))=>[hx|hx].
  - have [M [hDM hMD]] := finite_injective_linear_inverse_exists hb (hinj x hx).
    exists M=>_; split; last by split.
    exact (@norm_finite_linear_bounded R X X NX NX hNX hNX n b hb M).
  - exists 0=>ha; by exfalso; exact: hx ha.
have [E hE] := choice hex; by exists E.
Qed.
