(** Federer (1969), 1.7.6, p. 34: the norm of a top-degree exterior map is
    its value on every unit top vector. Dimension zero is included: the
    zeroth power is one-dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorGrading ExteriorMaps
  ExteriorDeterminant LinearBasis OperatorNormUP ExteriorOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonzero_top_vector_spans]: Federer 1.7.6,
    p. 34, supporting one-dimensionality: any nonzero top-degree
    vector spans the entire top power, by 1.3.4. *)
Lemma nonzero_top_vector_spans (R : fieldType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) n (b : 'I_n -> V) (hb : is_basis b)
    (u : exterior_power V n) : u != 0 -> forall x, exists c : R, x = c *: u.
Proof.
move=> hu x.
pose tc := @top_coordinate R h2 n V b hb.
have hue := @top_expansion R h2 n V b hb u.
have hxe := @top_expansion R h2 n V b hb x.
have hc : (tc u : R) != 0.
  apply/eqP=> hz; have hu0 : u = 0 by rewrite hue hz scale0r.
  by rewrite hu0 eqxx in hu.
exists ((tc x : R) / (tc u : R)); symmetry.
transitivity (((tc x : R) / (tc u : R)) *: (((tc u : R)) *: (@top_vector R n V b))).
- congr (_ *: _); exact hue.
- by rewrite scalerA divfK // -hxe.
Qed.

(** Source for [unit_spanning_operator_norm]: Federer 1.7.6,
    p. 34, supporting norm fact: on a one-dimensional source,
    every unit vector attains the operator norm. *)
Lemma unit_spanning_operator_norm (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) L (hL : is_operator_norm hB hC f L)
    u (hu : inner_norm hB u = 1)
    (hs : forall x, exists c : R, x = c *: u) : L = inner_norm hC (f u).
Proof.
apply: operator_norm_unique hL _; constructor.
- move=> x hx; have [c he] := hs x.
  rewrite he inner_normZ hu mulr1 in hx.
  rewrite he linearZ inner_normZ -[leRHS]mul1r.
  apply: ler_wpM2r; first exact: inner_norm_nonnegative.
  exact hx.
- exists u; split=> //; by rewrite hu.
Qed.

(** Source for [top_exterior_operator_unit_value]: Federer
    1.7.6, p. 34, if the degree equals dim V, then the norm
    of the induced map is its value at every unit top vector. *)
Theorem top_exterior_operator_unit_value (R : realType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U})
    (u : exterior_power V n) (hu : exterior_norm h2 hB u = 1) :
  exterior_operator_norm h2 hB hC hb f n =
    exterior_norm h2 hC (exterior_power_map f n u).
Proof.
apply: (@unit_spanning_operator_norm R (exterior_power V n) (exterior_power U n)
  (@exterior_inner_form R h2 V B hB n) (@exterior_inner_form R h2 U C hC n)
  (@exterior_inner_productP R h2 V B hB n) (@exterior_inner_productP R h2 U C hC n)
  (exterior_power_map f n) (exterior_operator_norm h2 hB hC hb f n)
  (exterior_operator_normP h2 hB hC hb f n) u hu).
have hun : u != 0 by rewrite -(exterior_norm_eq0 h2 hB) hu oner_eq0.
exact (@nonzero_top_vector_spans R h2 V n b hb u hun).
Qed.

(** Source for [top_exterior_operator_determinant]: Federer
    1.7.6, p. 34, for an endomorphism the top exterior
    operator norm is the absolute value of its determinant. *)
Theorem top_exterior_operator_determinant (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> V}) :
  exterior_operator_norm h2 hB hB hb f n = `|det h2 hb f|.
Proof.
pose hE := @exterior_inner_productP R h2 V B hB n.
pose u := inner_normalize hE (@top_vector R n V b).
have hu : exterior_norm h2 hB u = 1.
  apply: inner_normalize_norm; exact: top_vector_nonzero.
rewrite (@top_exterior_operator_unit_value R h2 V V B B hB hB n b hb f u hu).
by rewrite (@detE R h2 n V b hb f u) exterior_norm_scale hu mulr1.
Qed.
