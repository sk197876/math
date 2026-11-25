(** Local correction to Federer (1969), 2.6.5, p. 119. A null diagonal
    becomes an infinite-measure set after reassociating the product with a
    measure that is infinite on nonempty sets. We allow the diagonal over
    any positive-measure subset A, rather than only the whole real line. The
    diagonal-null hypothesis will be verified separately for Lebesgue
    measure. This is a local correction, not a correction in Federer's
    erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic MeasureSplit
  MeasurePushforward MeasureAlmostBasic MeasureFiniteClosure
  ProductMeasure ProductMeasureSequenceInfimum InfiniteProductProjection PositiveCoverMember.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_diagonal]: the diagonal D used in the
    counterexample. Supports the local correction to Federer 2.6.5, p. 119. *)
Definition restricted_diagonal (X : Type) (A : set X) : set (X * X) :=
  [set p | A p.1 /\ p.1 = p.2].

(** Source for [right_associated_diagonal]: local correction to Federer
    2.6.5, p. 119. *)
Definition right_associated_diagonal (X Z : Type) (A : set X) : set (X * (X * Z)) :=
  [set p | A p.1 /\ p.1 = p.2.1].

(** Source for [right_associated_diagonal_infinite]: The covering argument
    is the printed argument, supporting the local correction to Federer
    2.6.5, p. 119. *)
Lemma right_associated_diagonal_infinite (R : realType) (X Z : choiceType)
    (mu : set X -> \bar R) (gamma : set Z -> \bar R)
    (hm : is_measure mu) (hg : is_measure gamma)
    (hginf : forall C, (exists z, C z) -> gamma C = +oo)
    (z0 : Z) (A : set X) :
  0 < mu A ->
  product_measure hm (product_measure_is_measure hm hg)
    (@right_associated_diagonal X Z A) = +oo.
Proof.
move=> hA; apply/eqP; rewrite eq_le leey /=.
apply: (product_measure_sequence_cover_greatest hm (product_measure_is_measure hm hg))=> B E hBE hc.
pose D n := B n `&` product_first_projection (E n).
have hcover : A `<=` \bigcup_n D n.
  move=> x hx; have ht : @right_associated_diagonal X Z A (x,(x,z0)) by split.
  have [n _ [hxB hxE]] := hc (x,(x,z0)) ht.
  exists n=> //; split=> //; by exists z0.
have [n hn] := @positive_countable_cover_member R X mu hm A D hA hcover.
have hB : 0 < mu (B n).
  apply: lt_le_trans hn _; apply: (measure_mono hm)=> x [hx _]; exact hx.
have hE : 0 < mu (product_first_projection (E n)).
  apply: lt_le_trans hn _; apply: (measure_mono hm)=> x [_ hx]; exact hx.
have hi := @infinite_product_positive_projection R X Z mu gamma hm hg hginf (E n) hE.
have hv : mu (B n) * product_measure hm hg (E n) = +oo by rewrite hi gt0_muley.
rewrite -hv; exact: nonnegative_sum_term I.
Qed.

(** Source for [left_associated_null_diagonal]: Local correction to 2.6.5,
    p. 119. *)
Lemma left_associated_null_diagonal (R : realType) (X Z : choiceType)
    (mu : set X -> \bar R) (gamma : set Z -> \bar R)
    (hm : is_measure mu) (hg : is_measure gamma) (A : set X) :
  product_measure hm hm (restricted_diagonal A) = 0 ->
  product_measure (product_measure_is_measure hm hm) hg
    (restricted_diagonal A `*` @setT Z) = 0.
Proof.
move=> hD.
have hmeas := @measure_null_measurable R (X * X)%type
  (product_measure hm hm) (product_measure_is_measure hm hm) (restricted_diagonal A) hD.
have hb := @product_measure_rectangle_bound R (X * X)%type Z
  (product_measure hm hm) gamma (product_measure_is_measure hm hm) hg
  (restricted_diagonal A) setT hmeas (measure_measurable_whole hg).
rewrite hD mul0e in hb; apply/eqP; rewrite eq_le hb /=.
exact (measure_nonnegative (product_measure_is_measure (product_measure_is_measure hm hm) hg) _).
Qed.

(** Source for [product_measure_associativity_obstruction]: Supporting
    Federer 2.6.5, p. 119.The hypotheses retain precisely the positive-set,
    null-diagonal and infinite-factor properties used in the proof. *)
Theorem product_measure_associativity_obstruction (R : realType) (X Z : choiceType)
    (mu : set X -> \bar R) (gamma : set Z -> \bar R)
    (hm : is_measure mu) (hg : is_measure gamma)
    (hginf : forall C, (exists z, C z) -> gamma C = +oo)
    (z0 : Z) (A : set X) :
  0 < mu A -> product_measure hm hm (restricted_diagonal A) = 0 ->
  measure_pushforward (fun p : (X * X) * Z => (p.1.1,(p.1.2,p.2)))
    (product_measure (product_measure_is_measure hm hm) hg) <>
  product_measure hm (product_measure_is_measure hm hg).
Proof.
move=> hA hD he.
have hv := congr1 (fun nu => nu (@right_associated_diagonal X Z A)) he.
have hp : (fun p : (X * X) * Z => (p.1.1,(p.1.2,p.2))) @^-1`
    (@right_associated_diagonal X Z A) = restricted_diagonal A `*` @setT Z.
  apply/seteqP; split; move=> [[x y] z] /=.
  - by move=> h; split.
  - by move=> [h _].
rewrite /measure_pushforward hp
  (@left_associated_null_diagonal R X Z mu gamma hm hg A hD)
  (@right_associated_diagonal_infinite R X Z mu gamma hm hg hginf z0 A hA) in hv.
have hpos : (0 < +oo :> \bar R) by exact: ltry.
by rewrite -hv ltxx in hpos.
Qed.
