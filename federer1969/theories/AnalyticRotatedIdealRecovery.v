(** Federer (1969), 3.4.8(10), pp. 332–333:
    the printed assumption I=ideal(var I)
    also holds for I_g. Apply the
    actual rotated vanishing-ideal equation and
    the proved ideal-variety recovery theorem of 3.4.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing CommutativeIdealUP SetGermUP SetGermLaws
  GermVanishingSealed IdealVarietyGermSealed IdealVarietyVanishingLaws AnalyticRotatedGermIdeal
  AnalyticRotatedVanishingIdeal OrthogonalGroupHaarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [given_vanishing_ideal_variety_recovery]:
    a finitely generated ideal known to
    be the vanishing ideal of a
    set germ equals ideal(var I),
    3.4.5, p. 320, as used
    in 3.4.8(10), pp. 332–333. *)
Lemma given_vanishing_ideal_variety_recovery (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (I:set [the comNzRingType of (@analytic_germ_ring R X NX hNX a)])
    (hI:is_finitely_generated_commutative_ideal I)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  I = @AnalyticSetIdeal.value R X NX hNX a sigma ->
  I = @AnalyticSetIdeal.value R X NX hNX a (@IdealVarietyGerm.value R X NX hNX a I hI).
Proof.
move=>hEqual;move:hI;rewrite hEqual=>hI.
exact:esym (@vanishing_ideal_variety_recovery R X NX hNX a sigma hI).
Qed.

(** Source for [analytic_rotated_ideal_variety_recovery]:
    the original condition I=ideal(var I)
    transfers to I_g, supporting the
    nonempty-germ conclusion of 3.4.8(10),
    pp. 332–333. No recovery condition
    on the rotated ideal is added
    to the numbered theorem's hypotheses. *)
Theorem analytic_rotated_ideal_variety_recovery (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (I:set [the comNzRingType of (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)])
    (g:@orthogonal_group R X B hB n e he)
    (hI:is_finitely_generated_commutative_ideal I)
    (hIg:is_finitely_generated_commutative_ideal (@analytic_rotated_germ_ideal R X B hB n e he I g)):
  I = @AnalyticSetIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0
    (@IdealVarietyGerm.value R X (inner_norm hB) (inner_norm_real_norm hB) 0 I hI) ->
  @analytic_rotated_germ_ideal R X B hB n e he I g =
    @AnalyticSetIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0
      (@IdealVarietyGerm.value R X (inner_norm hB) (inner_norm_real_norm hB) 0
        (@analytic_rotated_germ_ideal R X B hB n e he I g) hIg).
Proof.
move=>hRecovered.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose Top:=Topological.clone (real_norm_metric_space hNX) _.
have [S hS]:=@set_germ_has_representative Top 0 (@IdealVarietyGerm.value R X NX hNX 0 I hI).
rewrite -hS in hRecovered.
have hRotated:@analytic_rotated_germ_ideal R X B hB n e he I g =
    @AnalyticSetIdeal.value R X NX hNX 0 (@set_germ Top 0
      ((@orthogonal_element_map R X B hB n e he g) @^-1` S)).
  rewrite hRecovered;exact:(@analytic_rotated_vanishing_ideal R X B hB n e he g S).
exact:(@given_vanishing_ideal_variety_recovery R X NX hNX 0 _ hIg _ hRotated).
Qed.
