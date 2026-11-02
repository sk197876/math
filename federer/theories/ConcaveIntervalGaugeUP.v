(** Federer (1969), 2.10.28, pp. 191–193: abstract laws for the continuous
    increasing strictly concave gauge h on the nonnegative real axis, with
    h(0)=0. Values of its total representative on negative inputs remain
    unspecified and are never used. Continuity is specified by the relative
    epsilon-delta law; no formula or additional project axiom for h is
    assumed. The corrected single-root hypothesis of (3) is separate:
    erratum p. 4, book p. 192 line 4. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_concave_interval_gauge]: direct
    gauge hypotheses in 2.10.28, p. 191,
    stated as laws before any particular Cantor
    construction. The order condition is weak
    monotonicity; strict monotonicity follows from
    strict concavity on the whole nonnegative axis. *)
Record is_concave_interval_gauge (R : realType) (h : R -> R) : Prop := {
  (** Source for [interval_gauge_zero]: direct
      h(0)=0 convention in 2.10.28, p. 191. *)
  interval_gauge_zero : h 0=0;
  (** Source for [interval_gauge_increasing]: direct
      increasing-gauge hypothesis in 2.10.28,
      p. 191, restricted to nonnegative inputs. *)
  interval_gauge_increasing : forall a b : R, 0<=a -> a<=b -> h a<=h b;
  (** Source for [interval_gauge_strict_concavity]: direct strict concavity on
    the nonnegative axis in 2.10.28, p. 191. *)
  interval_gauge_strict_concavity : forall a b t : R,
    0<=a -> 0<=b -> a!=b -> 0<t -> t<1 ->
    (1-t)*h a+t*h b<h ((1-t)*a+t*b);
  (** Source for [interval_gauge_continuity]: direct
      continuity hypothesis in 2.10.28, p. 191,
      expressed relatively to the nonnegative axis,
      including continuity from the right at zero. *)
  interval_gauge_continuity : forall x e : R, 0<=x -> 0<e ->
    exists d : R, 0<d /\ forall y : R, 0<=y -> `|y-x|<d -> `|h y-h x|<e
}.
