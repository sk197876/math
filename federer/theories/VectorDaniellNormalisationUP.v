(** Federer (1969), 2.5.12, printed p. 103: properties of a representing
    density chosen with unit dual norm almost everywhere and measurable dual
    norm. The proof on pp. 104–105 chooses values in the closed dual unit
    ball at every point. This additional representative convention
    simplifies downstream pairing estimates; almost uniqueness does not
    require it. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP MeasureAlmostUP MeasurableFunctionUP
  SummableRealFunctionUP VectorDaniellHypotheses VectorDaniellRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_normalised_vector_daniell_density]: the full
    representing-density conclusions of Federer 2.5.12, p. 103,
    with the everywhere unit-ball choice made on p. 104.
    These are proved properties of a witness, not project axioms. *)
Record is_normalised_vector_daniell_density (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (Q : set (X -> E)) (T : (X -> E) -> R)
    (k : X -> weak_dual_space hN) : Prop := {
  (** Source for [normalised_vector_density_laws]: weak
      measurability and the integral formula, Federer 2.5.12, p. 103. *)
  normalised_vector_density_laws : is_vector_daniell_density phi Q T k;
  (** Source for [normalised_vector_density_norm_measurable]:
      measurability of nu* o k, Federer 2.5.12, p. 103,
      proved by a countable supremum on p. 105. *)
  normalised_vector_density_norm_measurable :
    is_measure_measurable_function phi
      (real_total_integrand (fun x => dual_norm N (val (k x))));
  (** Source for [normalised_vector_density_unit_norm]:
      nu*[k(x)] = 1 almost everywhere, Federer 2.5.12,
      p. 103, proved in the last paragraph on p. 106. *)
  normalised_vector_density_unit_norm :
    measure_almost_everywhere phi [set x | dual_norm N (val (k x)) = 1];
  (** Source for [normalised_vector_density_bound]: the
      representative taking values in U*, Federer 2.5.12, p. 104. *)
  normalised_vector_density_bound : forall x, dual_norm N (val (k x)) <= 1
}.
