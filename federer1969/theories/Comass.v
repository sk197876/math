(** Federer (1969), 1.8.1, p. 38: public interface to the comass in finite
    dimension. The interface uses only the sealed supremum specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  AlternatingPairing SimpleUnitBall ComassUP ComassSealed LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Interface.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m)%N.

(** Source for [comass]: Federer 1.8.1, p. 38, the
    positive-degree comass supplied by its sealed supremum laws. *)
Definition comass (phi : A_m V R^o m) := @Comass.norm R h2 V B hB n e he m hm phi.

(** Source for [comassP]: Federer 1.8.1, p. 38, the
    public comass obeys its defining supremum specification. *)
Theorem comassP phi : is_comass h2 hB phi (comass phi).
Proof. exact: Comass.laws. Qed.

(** Source for [comass_supremum]: Federer 1.8.1, p. 38,
    first displayed equality: comass is the supremum of evaluations
    on simple vectors of norm at most one. *)
Theorem comass_supremum phi : comass phi =
  sup ((fun x => pairing x phi) @` (@simple_unit_ball R h2 V B hB m)).
Proof.
pose D := (fun x => pairing x phi) @` (@simple_unit_ball R h2 V B hB m).
have hn : D !=set0.
  exists (pairing 0 phi); exists 0 => //; exact: simple_unit_ball_zero.
have hb : ubound D (comass phi).
  move=> r [x hx <-]; exact (@comass_upper_law R h2 V B hB m phi (comass phi) (comassP phi) x hx).
have hu : has_sup D by split=> //; exists (comass phi).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@comass_least_upper_bound R h2 V B hB m phi (comass phi) (comassP phi) (sup D)) => x hx.
  apply: (sup_upper_bound hu); by exists x.
- exact: ge_sup hn hb.
Qed.

(** Source for [comass_basis_independent]: Federer 1.8.1,
    p. 38, the defining formula depends only on the inner product,
    not on a basis supplied to prove finite-dimensional existence. *)
Theorem comass_basis_independent k (f : 'I_k -> V) (hf : is_basis f) phi :
  comass phi = @Comass.norm R h2 V B hB k f hf m hm phi.
Proof. exact: comass_unique (comassP phi) (@Comass.laws R h2 V B hB k f hf m hm phi). Qed.
End Interface.
