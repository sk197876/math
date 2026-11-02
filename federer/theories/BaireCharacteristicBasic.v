(** Federer (1969), 2.2.15, p. 71: elementary closure steps for the family
    of sets with Baire characteristic functions. Complement and finite union
    are expressed using the proved real Baire algebra; uniqueness uses only
    the abstract characteristic laws. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CharacteristicFunctionUP
  BaireFunctions BaireRealAlgebra ClosedCharacteristicBaire.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [has_baire_characteristic]: the family F
    in Federer 2.2.15, pp. 70–71. Existence of a
    Baire function obeying the characteristic laws is equivalent to
    any chosen characteristic witness having that property. *)
Definition has_baire_characteristic (R : realType) (X : topologicalType) (A : set X) : Prop :=
  exists f : X -> real_line_metric R, is_characteristic_function A f /\ is_baire_function f.

(** Source for [baire_characteristic_transfer]: supporting witness
    independence for the family F of Federer 2.2.15,
    pp. 70–71; the characteristic function is unique. *)
Lemma baire_characteristic_transfer (R : realType) (X : topologicalType)
    (A : set X) (f : X -> real_line_metric R) :
  has_baire_characteristic R A -> is_characteristic_function A f -> is_baire_function f.
Proof.
move=> [g [hg hgb]] hf.
have he : f = g by apply: funext; exact: characteristic_function_unique hf hg.
by rewrite he.
Qed.

(** Source for [baire_characteristic_empty]: the empty member
    of the Borel family F in Federer 2.2.15, p. 71. *)
Lemma baire_characteristic_empty (R : realType) (X : topologicalType) :
  @has_baire_characteristic R X set0.
Proof.
exists (fun _ => 0); split; last exact: baire_real_constant.
constructor=> x; [by case|by move=> _].
Qed.

(** Source for [baire_characteristic_complement]: complement
    closure of the family F in Federer 2.2.15, p. 71.
    The complementary characteristic function is one minus the original. *)
Lemma baire_characteristic_complement (R : realType) (X : topologicalType) (A : set X) :
  has_baire_characteristic R A -> has_baire_characteristic R (~` A).
Proof.
move=> [f [hf hb]]; exists (fun x => 1 - f x); split.
- constructor=> x hx.
  + by rewrite (characteristic_off_set hf hx) subr0.
  + have ha : A x by apply: contrapT.
    by rewrite (characteristic_on_set hf ha) subrr.
- exact: baire_real_add (@baire_real_constant R X 1) (baire_real_opp hb).
Qed.

(** Source for [baire_characteristic_binary_union]: finite-union
    closure needed for the Borel family F in Federer 2.2.15,
    p. 71. Its characteristic function is one minus the
    product of the two complementary characteristic functions. *)
Lemma baire_characteristic_binary_union (R : realType) (X : topologicalType) (A B : set X) :
  has_baire_characteristic R A -> has_baire_characteristic R B ->
  has_baire_characteristic R (A `|` B).
Proof.
move=> [f [hf hfb]] [g [hg hgb]].
exists (fun x => 1 - (1 - f x) * (1 - g x)); split.
- constructor=> x hx.
  + case: hx=> hx.
    * by rewrite (characteristic_on_set hf hx) subrr mul0r subr0.
    * by rewrite (characteristic_on_set hg hx) subrr mulr0 subr0.
  + have ha : ~ A x by move=> ha; apply: hx; left.
    have hb : ~ B x by move=> hb; apply: hx; right.
    by rewrite (characteristic_off_set hf ha) (characteristic_off_set hg hb) !subr0 mul1r subrr.
- have hfc := baire_real_add (@baire_real_constant R X 1) (baire_real_opp hfb).
  have hgc := baire_real_add (@baire_real_constant R X 1) (baire_real_opp hgb).
  exact: baire_real_add (@baire_real_constant R X 1) (baire_real_opp (baire_real_mul hfc hgc)).
Qed.
