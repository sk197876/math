(** Federer (1969), 1.7.7, p. 34, last formula: transfer the simple-vector
    argument to simple covectors via gamma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP InnerPolarity InnerPolaritySurjection
  InnerExterior InnerExteriorProducts InnerExteriorPolarity SimpleCovectors
  SimpleElementary AssociatedSubspace FiniteExteriorPowers ExteriorGrading
  AlternatingCoordinates OneFormProducts ScalarCoefficients LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [simple_covector_polarity_preimage]: Federer
    1.7.7, p. 34, supporting covector version: every simple
    m-covector in finite dimension is gamma of a simple m-vector.
    Surjectivity of the degree-one polarity lifts its factors. *)
Theorem simple_covector_polarity_preimage (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) m (phi : A_m V R^o m) :
  simple_covector h2 phi -> exists x : exterior_power V m,
    simple x /\ inner_exterior_form h2 hB x = phi.
Proof.
move=> [alpha ->].
have he i := @inner_polarity_surjective R V B hB n b hb (alpha i).
pose e i := sval (constructive_indefinite_description (he i)).
have hp i : inner_polarity hB (e i) = alpha i :=
  svalP (constructive_indefinite_description (he i)).
exists (e_lambda e (ord_tuple m)); split; first exact: product_simple.
rewrite inner_exterior_product_covectors.
have hh : (fun i => inner_polarity hB (e i)) = alpha by apply: funext => i; exact: hp.
by rewrite hh.
Qed.
