(** Federer (1969), 2.3.1, p. 72: the conventions for "almost all", almost
    containment, and almost equality. These are predicates on the existing
    measure, not additional measure axioms. No erratum entry affects book p.
    72. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_almost_everywhere]: direct definition in
    Federer 2.3.1, p. 72, first display: the complement of the
    truth set has measure zero. No measurability premise is needed. *)
Definition measure_almost_everywhere (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (P : set X) : Prop := mu (~` P) = 0.

(** Source for [measure_almost_everywhere_on]: direct relative
    convention in Federer 2.3.1, p. 72, final paragraph:
    the exceptional subset A minus the truth set is null. *)
Definition measure_almost_everywhere_on (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A P : set X) : Prop := mu (A `\` P) = 0.

(** Source for [measure_almost_included]: direct last convention
    in Federer 2.3.1, p. 72: B contains almost all of A exactly
    when A minus B is null. Argument order follows inclusion A in B. *)
Definition measure_almost_included (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A B : set X) : Prop := mu (A `\` B) = 0.

(** Source for [measure_almost_equal]: direct function convention in Federer
    2.3.1, p. 72, middle paragraph. Equality means a common defined value *)
Definition measure_almost_equal (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (f g : partial_function X Y) : Prop :=
  measure_almost_everywhere mu (partial_function_agreement f g).
