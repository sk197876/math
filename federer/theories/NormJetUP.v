(** Federer (1969), 3.1.11, p. 221:
    the kth jet is the polynomial specified
    by the actual differentials at the base point.
    Existence is a theorem, not an axiom. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom PolynomialFunctions PolynomialRepresentations
  NormHigherDifferentialUP NormTaylorRemainderBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_norm_jet_polynomial]:
    the kth jet F_a in Federer
    3.1.11, p. 221, is
    the degree-at-most-k polynomial whose
    value is the divided-power Taylor sum
    of the actual differentials at a. *)
Record is_norm_jet_polynomial (R : realType)
    (X Y : lmodType R) (NX : X->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (A : X->Prop) (f : X->Y) k a (P : PolynomialFunction X Y) : Prop := {
  (** Source for [norm_jet_polynomial_degree]:
      the kth jet has degree at most k,
      Federer 3.1.11, p. 221. *)
  norm_jet_polynomial_degree : (polynomial_degree P<=k)%N;
  (** Source for [norm_jet_polynomial_expansion]:
      the displayed formula for F_a,
      Federer 3.1.11, p. 221.
      Every coefficient is an actual higher
      differential at the original base point. *)
  norm_jet_polynomial_expansion : exists D : forall i, Z i,
    (forall i, (i<=k)%N -> has_norm_higher_differential NX ev ZN A f i a (D i)) /\
    forall x, P x=norm_taylor_value ev (fun i _=>D i) a (x-a) k
}.
