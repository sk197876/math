(** Federer (1969), 2.4.12, p. 87: consequences of
    abstract finite Borel approximation laws, supporting finite-image density.
    The specification and source-edition details are in
    FiniteNearestApproximationUP.v. No proof here uses the recursion
    hidden behind FiniteNearestApproximationSealed.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import BorelFunctionUP BorelDiscreteIndexBasic FiniteNearestApproximationUP
  SeparableClosedCover PointwiseLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_nearest_map_borel]: measurable finite-partition
    approximants supporting Federer 2.4.12, p. 87 *)
Lemma finite_nearest_map_borel (R : realType) (Y : metricType R)
    (y : nat -> Y) (q : nat -> Y -> nat) :
  is_finite_nearest_approximation y q -> forall n, is_borel_function (fun x => y (q n x)).
Proof.
move=> h n; exact: borel_function_of_discrete_index (finite_nearest_fibres h n).
Qed.

(** Source for [finite_nearest_map_finite_image]: finite-image
    conclusion for the approximants in Federer 2.4.12, p. 87.
    The bound includes n=0, where there is only one candidate. *)
Lemma finite_nearest_map_finite_image (R : realType) (Y : metricType R)
    (y : nat -> Y) (q : nat -> Y -> nat) :
  is_finite_nearest_approximation y q -> forall n, finite_set ((fun x => y (q n x)) @` setT).
Proof.
move=> h n.
apply: (sub_finite_set (B:= y @` [set i : nat | (i <= n)%N])).
- move=> z [x _ <-]; exists (q n x)=> //; exact: finite_nearest_index_bound h n x.
- apply: finite_image.
  have he : [set i : nat | (i <= n)%N] = `I_n.+1 by apply/seteqP; split.
  rewrite he; exact: finite_II.
Qed.

(** Source for [finite_nearest_map_reference_bound]: supporting
    pointwise majorant for Federer 2.4.12, p. 87. Choosing
    the first candidate as zero gives approximation error at most the
    original norm, allowing an integrable powered-norm majorant. *)
Lemma finite_nearest_map_reference_bound (R : realType) (Y : metricType R)
    (y : nat -> Y) (q : nat -> Y -> nat) :
  is_finite_nearest_approximation y q -> forall n x,
    mdist x (y (q n x)) <= mdist x (y 0%N).
Proof. move=> h n x; exact (@finite_nearest_minimal R Y y q h n x 0%N (leq0n n)). Qed.

(** Source for [finite_nearest_map_converges]: supporting dense-sequence
    approximation for Federer 2.4.12, p. 87 Every nearby candidate is
    eventually in the finite prefix, so the nearest candidate converges to
    the input. *)
Lemma finite_nearest_map_converges (R : realType) (Y : metricType R)
    (y : nat -> Y) (q : nat -> Y -> nat) :
  is_finite_nearest_approximation y q -> dense (y @` setT) ->
  is_pointwise_limit (fun n x => y (q n x)) (@id Y).
Proof.
move=> h hd x U hU.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP x U) hU.
have [z [[i _ hi] hz]] := metric_dense_point_near hd x he.
exists i; first exact Logic.I.
move=> n hn; apply: hball.
apply: le_lt_trans (@finite_nearest_minimal R Y y q h n x i hn) _.
by rewrite hi.
Qed.
