(** Federer (1969), 4.1.9, p. 363: specify the
    compact replacements used in the original test-action
    restatement. Agreement holds near the whole source
    support. Existence is proved separately from the printed
    properness hypothesis on the closed time cylinder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentHomotopyUP CurrentHomotopyTransgressionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTestReplacementUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu k j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation F := (@current_smooth_space R h2 nu V hV (1+j)).
Local Notation fv := (@current_smooth_value R h2 nu V hV (1+j)).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation KH := (@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hHomotopy).

Local Notation D := (@current_test_space R h2 n U hU j).
Local Notation value := (@current_test_value R h2 n U hU j).
Variable T:@current_space R h2 n U hU k.

(** Source for [is_current_homotopy_test_replacement]: an
    actual compact test agrees with the original smooth
    homotopy form on an open neighbourhood of the whole
    current support, supporting the test-action restatement
    in Federer 4.1.9, p. 363. This independent
    predicate assumes neither a cutoff nor its existence. *)
Definition is_current_homotopy_test_replacement (psi:F) (beta:D):Prop:=
  exists W:set X,@open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W /\
    @current_support R h2 n U hU k T `<=` W /\ W `<=` U /\
    forall x,W x->value beta x=ev (KH psi) x.
End CurrentHomotopyTestReplacementUP.
