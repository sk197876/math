(** Supporting result for Federer (1969), 2.7.18, printed p. 141, and 2.7.1,
    p. 122: if p : X -> Y is a bijection with inverse q, and f o q belongs
    to L_Y whenever f belongs to L_X, then the image measure p_#(phi) of
    2.1.2, p. 54, is L_Y regular in the sense of 2.5.3, p. 94, whenever phi
    is L_X regular. The families F0, F1, F2 of 2.5.3 are carried onto each
    other by S |-> q^{-1}(S), since q^{-1}{x : t < f(x)} = {y : t < (f o
    q)(y)}; the proof is that of lattice_regular_inverse_pushforward for
    2.7.17. This applies to the homeomorphisms A_g of 2.7.1 and L_X = L_Y =
    K(X); it is what makes the identity A_g#(gamma) = chi(g) gamma of 2.7.1
    hold for measures, by the uniqueness in 2.5.3. Federer uses this without
    comment. Unlike the continuous proper maps of 2.5.19, p. 113, whose
    image measures need not be regular (DaniellSpaceImageRegularity.v), the
    bijectivity of p is essential here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal.
From Federer Require Import FunctionLatticeRegularityUP MeasurePushforward
  InvariantMeasureTranslates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section RegularPushforwardBijection.
Variable R : realType.
Variables X Y : choiceType.
Variables (LX : set (X -> R)) (LY : set (Y -> R)).
Variables (p : X -> Y) (q : Y -> X).
Hypothesis hpq : cancel p q.
Hypothesis hqp : cancel q p.
Hypothesis hL : forall f, LX f -> LY (f \o q).

(** Source for [bijection_pushforward_regular]: p_#(phi) is L_Y
    regular whenever phi is L_X regular, Federer 2.5.3, p. 94, as
    needed for A_g#(gamma) in 2.7.1, p. 122, and 2.7.18, p. 141. The
    statement is that of lattice_regular_inverse_pushforward, proved for
    2.7.17 in InvariantMeasureTranslates.v. *)
Theorem bijection_pushforward_regular (mu : set X -> \bar R) :
  is_function_lattice_regular LX mu -> is_function_lattice_regular LY (measure_pushforward p mu).
Proof. exact: (lattice_regular_inverse_pushforward hpq hqp hL). Qed.

End RegularPushforwardBijection.
