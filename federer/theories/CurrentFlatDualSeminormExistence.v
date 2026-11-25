(** Federer (1969), 4.1.12, p. 367: the
    original dual flat seminorm exists for every real
    linear functional. Reuse the preceding opaque
    extended supremum; zero is an admissible test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet ExtendedSupremumSealed
  CurrentFlatFormSeminormLaws CurrentFlatDualSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatDualSeminormExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation F := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation hF := (@current_flat_test_is_seminorm R h2 n m U hU K).
Local Notation Values := (@current_flat_dual_values R h2 n m U hU K).

(** Source for [current_flat_dual_values_nonempty]: the
    zero test is admissible in the original dual
    supremum, supporting Federer 4.1.12, p. 367,
    including empty K and empty U. *)
Lemma current_flat_dual_values_nonempty (T:Hom DT R^o):Values T !=set0.
Proof.
exists 0;exists (0:DT);split.
- by rewrite (real_seminorm_zero hF) ler01.
- exact:linear0.
Qed.

(** Source for [current_flat_dual_seminorm_exists]: the
    original F_K(T) exists, possibly infinitely, for
    every real linear functional, Federer 4.1.12,
    p. 367. No continuity is imposed. *)
Theorem current_flat_dual_seminorm_exists (T:Hom DT R^o):
  exists c: \bar R,@is_current_flat_dual_seminorm R h2 n m U hU K T c.
Proof.
exists (@ExtendedSupremum.value R (Values T) (current_flat_dual_values_nonempty T)).
exact:ExtendedSupremum.laws.
Qed.
End CurrentFlatDualSeminormExistence.
