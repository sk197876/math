(** Federer (1969), 2.5.5, p. 96: positive and negative variations specified
    by their supremum and infimum laws on L+. This specification is
    independent of the existence construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_interval_values]: image of the positive order
    interval under mu in the first variation formula of Federer 2.5.5, p. 96 *)
Definition daniell_interval_values (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (f : X -> R) :=
  [set v : \bar R | exists k, lattice_positive_order_interval L f k /\ v=(A k)%:E].

(** Source for [is_daniell_positive_variation]: exact supremum formula on L+
    in Federer 2.5.5, p. 96 Off-lattice values are irrelevant; the real
    codomain records the finiteness proved from the hypotheses. *)
Definition is_daniell_positive_variation (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R) :=
  forall f, positive_function_lattice L f ->
    is_extended_real_supremum (daniell_interval_values L A f) (P f)%:E.

(** Source for [is_daniell_negative_variation]: negative infimum in Federer
    2.5.5, p. 96, expressed as the positive variation of -mu, as in its
    proof on p. 97 *)
Definition is_daniell_negative_variation (R : realType) (X : Type)
    (L : set (X -> R)) (A Q : (X -> R) -> R) :=
  is_daniell_positive_variation L (fun f => (- A f)%R) Q.
