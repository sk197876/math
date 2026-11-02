(** Federer (1969), 3.2.20, p. 257: independent laws
    needed to sum the compact-chart integral transformations. The
    geometric application proves every field from earlier theorems. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic NonnegativeSum
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_countable_area_decomposition]: supporting independent
    specification for the final summation in Federer 3.2.20,
    p. 257. Source densities are finite real values; target
    multiplicities may be infinite on a null set. A record value
    must prove all these laws and introduces no unproved axiom. *)
Record is_countable_area_decomposition (R : realType) (X Y Z : choiceType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (u : X -> Z) (v : Y -> Z) (p : X -> R) (pi : nat -> X -> R)
    (N : Y -> \bar R) (Ni : nat -> Y -> \bar R) : Prop := {
  (** Source for [area_decomposition_source_nonnegative]: nonnegative
      Jacobian density, Federer 3.2.20, p. 257. *)
  area_decomposition_source_nonnegative : forall x,(0<=p x)%R;
  (** Source for [area_decomposition_source_piece_bounds]: disjoint
      density pieces are dominated by the full source density,
      supporting the summation in 3.2.20, p. 257. *)
  area_decomposition_source_piece_bounds : forall i x,(0<=pi i x<=p x)%R;
  (** Source for [area_decomposition_source_measurable]: measurable
      full Jacobian density, proved from the compact-chart
      transformations in 3.2.20, p. 257. *)
  area_decomposition_source_measurable : is_measure_measurable_function mu
    (partial_function_total (fun x=>(p x)%:E : extended_real_line R));
  (** Source for [area_decomposition_source_pieces_measurable]: local
      measurable densities in 3.2.20, p. 257. *)
  area_decomposition_source_pieces_measurable : forall i,is_measure_measurable_function mu
    (partial_function_total (fun x=>(pi i x)%:E : extended_real_line R));
  (** Source for [area_decomposition_source_sum]: source density
      sum outside the null uncovered remainder, 3.2.20, p. 257. *)
  area_decomposition_source_sum : measure_almost_everywhere mu
    [set x|nonnegative_sum setT (fun i=>(pi i x)%:E)=(p x)%:E];
  (** Source for [area_decomposition_target_nonnegative]: nonnegative
      fibre count in 3.2.20, p. 257. *)
  area_decomposition_target_nonnegative : forall y,0<=N y;
  (** Source for [area_decomposition_target_piece_bounds]: subfibre
      counts are dominated by the original fibre count, supporting
      the summation in 3.2.20, p. 257. *)
  area_decomposition_target_piece_bounds : forall i y,0<=Ni i y<=N y;
  (** Source for [area_decomposition_target_measurable]: measurable
      full fibre count in 3.2.20, p. 257, supported also
      by the finite-mass version of 2.10.11, p. 176. *)
  area_decomposition_target_measurable : is_measure_measurable_function nu
    (partial_function_total (fun y=>(N y:extended_real_line R)));
  (** Source for [area_decomposition_target_pieces_measurable]: chart
      count measurability from 3.2.3 in the proof of 3.2.20,
      p. 257. *)
  area_decomposition_target_pieces_measurable : forall i,is_measure_measurable_function nu
    (partial_function_total (fun y=>(Ni i y:extended_real_line R)));
  (** Source for [area_decomposition_target_finite_almost]: finite
      multiplicity outside a null set in 3.2.20, p. 257,
      with the global finite-mass consequence supplied by 2.10.11. *)
  area_decomposition_target_finite_almost : measure_almost_everywhere nu [set y|N y< +oo];
  (** Source for [area_decomposition_target_sum]: fibre counts sum
      outside the image of the source null remainder, the final
      step of 3.2.20, p. 257. *)
  area_decomposition_target_sum : measure_almost_everywhere nu
    [set y|nonnegative_sum setT (fun i=>Ni i y)=N y];
  (** Source for [area_decomposition_local_transform]: the two
      local integral transformations in 3.2.20, p. 257.
      Their proof is required separately for each chart. *)
  area_decomposition_local_transform : forall (g : Z -> \bar R) i a,
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* (pi i x)%:E : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* Ni i y : extended_real_line R)) a
}.
