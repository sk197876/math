(** Federer (1969), 2.2.15, p. 71: the sum over integer j of (j/i) times the
    cell characteristic function. We reindex integers by their standard
    countable codes and use finite partial sums. The checked partial inverse
    of the code inserts zero terms at missing indices and never repeats an
    integer. Disjoint cells leave one possible active term at each point, so
    the partial sums are eventually constant. *)
From mathcomp Require Import all_boot all_algebra ssrint boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CharacteristicFunctionUP
  BaireFunctions BaireRealAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [integer_characteristic_term]: supporting natural-
    index form of the integer sum in Federer 2.2.15,
    p. 71. Missing integer-code indices contribute zero. *)
Definition integer_characteristic_term (R : realType) (X : Type)
    (c : int -> R) (g : int -> X -> R) n (x : X) : real_line_metric R :=
  if @pickle_inv int n is Some j then c j * g j x else 0.

(** Source for [integer_characteristic_term_baire]: supporting
    Baire property of each summand in Federer 2.2.15,
    p. 71, by scalar closure of the real Baire algebra. *)
Lemma integer_characteristic_term_baire (R : realType) (X : topologicalType)
    (c : int -> R) (g : int -> X -> real_line_metric R) :
  (forall j, is_baire_function (g j)) -> forall n,
  is_baire_function (integer_characteristic_term c g n).
Proof.
move=> hg n; rewrite /integer_characteristic_term; case: (@pickle_inv int n)=> [j|].
- exact: baire_real_scale (hg j).
- exact: baire_real_constant.
Qed.

(** Source for [integer_characteristic_term_at]: supporting
    value of the unique active summand in Federer 2.2.15,
    p. 71. The integer's own code decodes to that integer. *)
Lemma integer_characteristic_term_at (R : realType) (X : Type)
    (A : int -> set X) (g : int -> X -> R) (c : int -> R) x j :
  (forall l, is_characteristic_function (A l) (g l)) -> A j x ->
  integer_characteristic_term c g (pickle j) x = c j.
Proof.
move=> hg hx; rewrite /integer_characteristic_term pickleK_inv.
by rewrite (characteristic_on_set (hg j) hx) mulr1.
Qed.

(** Source for [integer_characteristic_term_off]: supporting
    vanishing of all other summands in Federer 2.2.15,
    p. 71, when a point lies in a unique integer cell. *)
Lemma integer_characteristic_term_off (R : realType) (X : Type)
    (A : int -> set X) (g : int -> X -> R) (c : int -> R) x j n :
  (forall l, is_characteristic_function (A l) (g l)) ->
  (forall l, A l x -> l = j) -> n <> pickle j ->
  integer_characteristic_term c g n x = 0.
Proof.
move=> hg hcell hn; rewrite /integer_characteristic_term.
case he : (@pickle_inv int n)=> [l|] //.
have hcode : pickle l = n.
  have hh := @pickle_invK int n; by rewrite he in hh.
have hl : ~ A l x.
  move=> hx; have hlj := hcell l hx; apply: hn; by rewrite -hcode hlj.
by rewrite (characteristic_off_set (hg l) hl) mulr0.
Qed.

(** Source for [finite_single_supported_sum]: supporting finite-
    sum identity for the integer-cell approximation in Federer
    2.2.15, p. 71. Once a partial sum includes
    the sole possible active index, it equals that summand. *)
Lemma finite_single_supported_sum (R : realType) (u : nat -> R) j a n :
  u j = a -> (forall k, k <> j -> u k = 0) -> (j < n)%N ->
  \sum_(i < n) u i = a.
Proof.
move=> hu hz hj.
pose ij := @Ordinal n j hj.
have hsum : \sum_(i < n | i != ij) u i = 0.
  apply: big1=> i hi; apply: hz=> he.
  have hie : i = ij by apply: val_inj; exact he.
  by rewrite hie eqxx in hi.
by rewrite (bigD1 ij) // hsum /= addr0 /ij /= hu.
Qed.
