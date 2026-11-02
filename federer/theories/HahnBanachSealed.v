(** Federer (1969), 1.10.5, p. 48: encapsulated supporting
    Hahn-Banach extension, using the finite-valued case of 2.4.12,
    p. 86. Source correspondence and editions: DominatedGraphExtension.v.
    The implementation proves the signature laws; they are not new axioms. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP PartialLinearMap DominatedGraphExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Module Type HAHN_BANACH.
(** Source for [extension]: Federer 1.10.5, p. 48, supporting
    dominated linear extension from 2.4.12, p. 86. *)
Parameter extension : forall (R : realType) (V : lmodType R)
  (N : V -> R), is_real_seminorm N -> forall G : V -> R^o -> Prop,
  linear_graph G -> (forall x a, G x a -> a<=N x) -> {linear V -> R^o}.
(** Source for [agreement]: Federer 1.10.5, p. 48, the extension
    agrees with the old graph as required by 2.4.12, p. 86. *)
Parameter agreement : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_seminorm N) (G : V -> R^o -> Prop)
  (hG : linear_graph G) (hdom : forall x a, G x a -> a<=N x) x a,
  G x a -> @extension R V N hN G hG hdom x=a.
(** Source for [bound]: Federer 1.10.5, p. 48, domination holds
    on the entire vector space, as in 2.4.12, p. 86. *)
Parameter bound : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_seminorm N) (G : V -> R^o -> Prop)
  (hG : linear_graph G) (hdom : forall x a, G x a -> a<=N x) x,
  @extension R V N hN G hG hdom x<=N x.
End HAHN_BANACH.
Module HahnBanach : HAHN_BANACH.
(** Source for [extension]: Federer 1.10.5, p. 48, the proved
    maximal-graph construction supplies the abstract extension map. *)
Definition extension (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (G : V -> R^o -> Prop)
    (hG : linear_graph G) (hdom : forall x a, G x a -> a<=N x) : {linear V -> R^o} :=
  GRing.Linear.clone _ _ _ _ (@dominated_linear_extension R V N hN G hG hdom) _.
(** Source for [agreement]: Federer 1.10.5, p. 48, the proved
    agreement law discharges the corresponding signature obligation. *)
Lemma agreement (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (G : V -> R^o -> Prop)
    (hG : linear_graph G) (hdom : forall x a, G x a -> a<=N x) x a :
  G x a -> @extension R V N hN G hG hdom x=a.
Proof. exact: dominated_linear_extensionE. Qed.
(** Source for [bound]: Federer 1.10.5, p. 48, the proved
    domination law discharges the corresponding signature obligation. *)
Lemma bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (G : V -> R^o -> Prop)
    (hG : linear_graph G) (hdom : forall x a, G x a -> a<=N x) x :
  @extension R V N hN G hG hdom x<=N x.
Proof. exact: dominated_linear_extension_bound. Qed.
End HahnBanach.
