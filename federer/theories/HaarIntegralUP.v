(** Federer (1969), 2.7.2, printed p. 122: "Two important special cases
    occur when X = G and the multiplication of G is used to define either
    (1) A(g,x) = gx, or (2) A(g,x) = xg^{-1} whenever g in G and x in G. In
    case (1), A_g is left multiplication by g. To this action correspond the
    so-called left chi covariant (invariant) integrals and measures. In
    particular, a nonzero monotone left invariant integral (measure) is
    called a left Haar integral (measure) of G. In case (2), A_g is right
    multiplication by g^{-1}. To this action correspond the so-called right
    chi covariant (invariant) integrals and measures. In particular, a
    nonzero monotone right invariant integral (measure) is called a right
    Haar integral (measure) of G." The two actions are written in the
    curried form of HomogeneousSpaceUP.v, so that the action applied to g is
    Federer's A_g. The covariant and invariant notions are those of
    CovariantIntegralUP.v for these actions. A nonzero integral mu on K(X)
    is one with mu(u) <> 0 for some u in K(X). A nonzero monotone invariant
    measure is read as the K(X) regular measure associated with a nonzero
    monotone invariant integral, in accordance with the definition of
    invariant measures in 2.7.1, p. 122; HaarIntegralLaws.v shows that such
    a measure is an invariant measure and is not the zero measure. The
    generic predicates for an arbitrary action also serve 2.7.4, p. 123, "a
    nonzero monotone invariant integral on K(X)". That the two actions make
    G a homogeneous space is proved in GroupMultiplicationHomogeneous.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import MonotoneDaniellIntegralUP CompactSupportFunctionUP
  FunctionLatticeRegularityUP RealIntegralFunctionalUP MeasureUP CovariantIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [left_multiplication_action]: Federer 2.7.2, p. 122,
    "(1) A(g,x) = gx whenever g in G and x in G"; "In case (1), A_g is
    left multiplication by g". Direct definition, curried. *)
Definition left_multiplication_action (G : Type) (mul : G -> G -> G) : G -> G -> G :=
  fun g x => mul g x.

(** Source for [right_multiplication_action]: Federer 2.7.2, p. 122,
    "(2) A(g,x) = xg^{-1} whenever g in G and x in G"; "In case (2), A_g
    is right multiplication by g^{-1}". Direct definition, curried. *)
Definition right_multiplication_action (G : Type) (mul : G -> G -> G) (inv : G -> G) :
    G -> G -> G :=
  fun g x => mul x (inv g).

(** Source for [is_nonzero_monotone_invariant_integral]: the phrase
    "a nonzero monotone left invariant integral" of Federer 2.7.2,
    p. 122, for an arbitrary action A, as also in 2.7.4, p. 123, "a
    nonzero monotone invariant integral on K(X)". Definition: an
    invariant integral in the sense of 2.7.1 which is a monotone Daniell
    integral on K(X) and does not vanish on K(X). *)
Record is_nonzero_monotone_invariant_integral (R : realType) (G : Type) (X : topologicalType)
    (A : G -> X -> X) (mu : (X -> R) -> R) : Prop := {
  (** Source for [nonzero_invariant_integral_invariant]: "invariant
      integral", Federer 2.7.1-2.7.2, p. 122. *)
  nonzero_invariant_integral_invariant : is_invariant_integral A mu;
  (** Source for [nonzero_invariant_integral_monotone]: "monotone",
      Federer 2.7.2, p. 122, in the sense of 2.5.2, p. 92. *)
  nonzero_invariant_integral_monotone :
    is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) mu;
  (** Source for [nonzero_invariant_integral_nonzero]: "nonzero",
      Federer 2.7.2, p. 122: mu(u) <> 0 for some u in K(X). *)
  nonzero_invariant_integral_nonzero :
    exists2 u, @compactly_supported_continuous_functions R X u & mu u <> 0
}.

(** Source for [is_nonzero_monotone_invariant_measure]: "a nonzero
    monotone left invariant ... measure", Federer 2.7.2, p. 122, for an
    arbitrary action A. Definition, following "The K(X) regular measure
    associated with a monotone chi covariant (invariant) integral is
    termed a chi covariant (invariant) measure" of 2.7.1, p. 122: phi is
    the K(X) regular measure representing a nonzero monotone invariant
    integral. Interpretation of the parenthetical "(measure)". *)
Definition is_nonzero_monotone_invariant_measure (R : realType) (G : Type) (X : topologicalType)
    (A : G -> X -> X) (phi : set X -> \bar R) : Prop :=
  exists mu : (X -> R) -> R,
    [/\ is_nonzero_monotone_invariant_integral A mu,
      is_measure phi,
      is_real_integral_functional phi (@compactly_supported_continuous_functions R X) mu &
      is_function_lattice_regular (@compactly_supported_continuous_functions R X) phi].

Section LeftRight.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G).

(** Source for [is_left_covariant_integral]: "In case (1) ... To this
    action correspond the so-called left chi covariant ... integrals",
    Federer 2.7.2, p. 122. Direct definition. *)
Definition is_left_covariant_integral (chi : G -> R) (mu : (G -> R) -> R) : Prop :=
  is_covariant_integral (left_multiplication_action mul) chi mu.

(** Source for [is_left_invariant_integral]: the left invariant
    integrals of Federer 2.7.2, p. 122. Direct definition. *)
Definition is_left_invariant_integral (mu : (G -> R) -> R) : Prop :=
  is_invariant_integral (left_multiplication_action mul) mu.

(** Source for [is_left_covariant_measure]: the left chi covariant
    measures of Federer 2.7.2, p. 122. Direct definition. *)
Definition is_left_covariant_measure (chi : G -> R) (phi : set G -> \bar R) : Prop :=
  is_covariant_measure (left_multiplication_action mul) chi phi.

(** Source for [is_left_invariant_measure]: the left invariant
    measures of Federer 2.7.2, p. 122. Direct definition. *)
Definition is_left_invariant_measure (phi : set G -> \bar R) : Prop :=
  is_invariant_measure (left_multiplication_action mul) phi.

(** Source for [is_left_haar_integral]: "a nonzero monotone left
    invariant integral ... is called a left Haar integral ... of G",
    Federer 2.7.2, p. 122. Direct definition. *)
Definition is_left_haar_integral (mu : (G -> R) -> R) : Prop :=
  is_nonzero_monotone_invariant_integral (left_multiplication_action mul) mu.

(** Source for [is_left_haar_measure]: "a nonzero monotone left
    invariant ... (measure) is called a left Haar ... (measure) of G",
    Federer 2.7.2, p. 122. Definition through
    is_nonzero_monotone_invariant_measure. *)
Definition is_left_haar_measure (phi : set G -> \bar R) : Prop :=
  is_nonzero_monotone_invariant_measure (left_multiplication_action mul) phi.

(** Source for [is_right_covariant_integral]: "In case (2) ... To
    this action correspond the so-called right chi covariant ...
    integrals", Federer 2.7.2, p. 122. Direct definition. *)
Definition is_right_covariant_integral (chi : G -> R) (mu : (G -> R) -> R) : Prop :=
  is_covariant_integral (right_multiplication_action mul inv) chi mu.

(** Source for [is_right_invariant_integral]: the right invariant
    integrals of Federer 2.7.2, p. 122. Direct definition. *)
Definition is_right_invariant_integral (mu : (G -> R) -> R) : Prop :=
  is_invariant_integral (right_multiplication_action mul inv) mu.

(** Source for [is_right_covariant_measure]: the right chi covariant
    measures of Federer 2.7.2, p. 122. Direct definition. *)
Definition is_right_covariant_measure (chi : G -> R) (phi : set G -> \bar R) : Prop :=
  is_covariant_measure (right_multiplication_action mul inv) chi phi.

(** Source for [is_right_invariant_measure]: the right invariant
    measures of Federer 2.7.2, p. 122. Direct definition. *)
Definition is_right_invariant_measure (phi : set G -> \bar R) : Prop :=
  is_invariant_measure (right_multiplication_action mul inv) phi.

(** Source for [is_right_haar_integral]: "a nonzero monotone right
    invariant integral ... is called a right Haar integral ... of G",
    Federer 2.7.2, p. 122. Direct definition. *)
Definition is_right_haar_integral (mu : (G -> R) -> R) : Prop :=
  is_nonzero_monotone_invariant_integral (right_multiplication_action mul inv) mu.

(** Source for [is_right_haar_measure]: "a nonzero monotone right
    invariant ... (measure) is called a right Haar ... (measure) of G",
    Federer 2.7.2, p. 122. Definition through
    is_nonzero_monotone_invariant_measure. *)
Definition is_right_haar_measure (phi : set G -> \bar R) : Prop :=
  is_nonzero_monotone_invariant_measure (right_multiplication_action mul inv) phi.

End LeftRight.
