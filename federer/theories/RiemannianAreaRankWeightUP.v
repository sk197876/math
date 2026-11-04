(** Federer (1969), 3.2.5(1), p. 245, as used
    in 3.2.46, p. 282: specify the auxiliary
    positive-rank cutoff by independent on/off laws.
    Its existence and measurability are separate proofs;
    no global auxiliary weight or derivative field is selected. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianLocalAreaSelection
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_riemannian_area_rank_weight]: independent
    laws for the auxiliary cutoff in 3.2.5(1),
    p. 245, with the actual original positive-Jacobian
    locus required by 3.2.46, p. 282. *)
Record is_riemannian_area_rank_weight (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R)
    (w : riemannian_metric_space hg -> extended_real_line R) : Prop := {
  (** Source for [riemannian_area_rank_weight_on]: retain
      the original weight on S and the actual positive
      Jacobian locus, supporting 3.2.46, p. 282. *)
  riemannian_area_rank_weight_on : forall x, S x -> positive_riemannian_area_locus f x ->
    w x=(u (f x))%:E;
  (** Source for [riemannian_area_rank_weight_off]: zero
      on the discarded source part in 3.2.5, p. 245,
      supporting 3.2.46, p. 282. *)
  riemannian_area_rank_weight_off : forall x, ~ (S x /\ positive_riemannian_area_locus f x) -> w x=0
}.

(** Source for [riemannian_area_rank_weight_graph]: exact
    graph law for the double cutoff in the proof of
    3.2.5(1), p. 245, with the original locus
    in 3.2.46, p. 282. It follows solely from
    the independent on/off laws and prior sealed cutoffs. *)
Lemma riemannian_area_rank_weight_graph (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) S u w :
  is_riemannian_area_rank_weight f S u w -> forall x z,
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) S
    (partial_function_zero_extension (0 : extended_real_line R) (positive_riemannian_area_locus f)
      (partial_function_total (fun x=>((u (f x))%:E : extended_real_line R))))) x z <-> w x=z.
Proof.
move=> hW x z; case: (pselect (S x))=> hS.
- rewrite (partial_function_zero_extension_on _ _ _ hS).
  case: (pselect (positive_riemannian_area_locus f x))=> hP.
  + rewrite (partial_function_zero_extension_on _ _ _ hP).
    change ((u (f x))%:E=z <-> w x=z); by rewrite (riemannian_area_rank_weight_on hW hS hP).
  + rewrite (partial_function_zero_extension_off _ _ _ hP)
      (riemannian_area_rank_weight_off hW (fun hx=>hP hx.2)).
    by split=> ->.
- rewrite (partial_function_zero_extension_off _ _ _ hS)
    (riemannian_area_rank_weight_off hW (fun hx=>hS hx.1)).
  by split=> ->.
Qed.

(** Source for [riemannian_area_rank_weight_nonnegative]:
    a nonnegative original weight keeps its sign under
    this cutoff, supporting 3.2.46, p. 282, and
    the characteristic approximation in 3.2.5, p. 245. *)
Lemma riemannian_area_rank_weight_nonnegative (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) S u w :
  is_riemannian_area_rank_weight f S u w -> (forall y, (0<=u y)%R) -> forall x, 0<=w x.
Proof.
move=> hW hU x; case: (pselect (S x /\ positive_riemannian_area_locus f x))=> hx.
- rewrite (riemannian_area_rank_weight_on hW hx.1 hx.2) lee_fin; exact: hU.
- by rewrite (riemannian_area_rank_weight_off hW hx).
Qed.
