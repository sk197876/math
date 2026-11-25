(** Federer (1969), 3.4.8(11), p. 334:
    independent laws of the original finite family
    of prepared W_j equations. Actual representatives,
    positive degrees, prefix coefficient domains and
    vanishing centre values precede their existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology NormAnalyticUP
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticPrefixCoordinatesSealed AnalyticRotatedGermIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TailLaws.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation Y:=(fun j:'I_n=>R_n R j).
Local Notation NY:=(fun j:'I_n=>inner_norm (@euclidean_inner_productP R j)).
Local Notation hNY:=(fun j:'I_n=>inner_norm_real_norm (@euclidean_inner_productP R j)).
Variable I:set (@analytic_germ_ring R X NX hNX 0).
Variable g:@orthogonal_group R X B hB n e he.
Variable m:nat.
Variable degree:'I_n->nat.
Variable U:forall j:'I_n,set (Y j).
Variable b:forall j:'I_n,'I_(degree j)->@analytic_representative_type R (Y j) (NY j) (hNY j) 0.
Variable f:'I_n->@analytic_representative_type R X NX hNX 0.

(** Source for [is_analytic_prepared_reduction_tail]:
    the original Weierstrass equation family used
    for the nested radii in 3.4.8(11),
    pp. 334–335. Inactive indices impose no
    positive-degree or coefficient condition. *)
Record is_analytic_prepared_reduction_tail:Prop:={
  (** Source for [analytic_prepared_tail_ideal]:
      each actual equation germ lies in I_g,
      3.4.8(11), p. 334. *)
  analytic_prepared_tail_ideal:forall j:'I_n,
    @analytic_rotated_germ_ideal R X B hB n e he I g (analytic_germ (f j));
  (** Source for [analytic_prepared_tail_positive]:
      the original r(j) is positive,
      3.4.8(11), p. 334. *)
  analytic_prepared_tail_positive:forall j:'I_n,(m<=j)%N ->(0<degree j)%N;
  (** Source for [analytic_prepared_tail_domains]:
      original coefficient domains contain zero and
      are open, 3.4.8(11), p. 334. *)
  analytic_prepared_tail_domains:forall j:'I_n,(m<=j)%N ->
    (@U j) 0 /\@open (real_norm_metric_space (hNY j)) ((@U j));
  (** Source for [analytic_prepared_tail_coefficients]:
      the original M_ij are analytic in the
      preceding prefix, 3.4.8(11), p. 334. *)
  analytic_prepared_tail_coefficients:forall j:'I_n,(m<=j)%N ->forall i,
    @norm_analytic R (Y j) R^o (NY j) (fun z:R^o=>`|z|) (hNY j)
      (@scalar_absolute_value_norm R) ((@U j)) (analytic_representative_value ((@b j i)));
  (** Source for [analytic_prepared_tail_zero]:
      M_ij(0)=0 from preparation, used in
      3.4.8(11), p. 334. *)
  analytic_prepared_tail_zero:forall j:'I_n,(m<=j)%N ->forall i,
    analytic_representative_value ((@b j i)) 0 = 0;
  (** Source for [analytic_prepared_tail_formula]:
      the exact original monic W_j formula,
      3.4.8(11), pp. 334–335. *)
  analytic_prepared_tail_formula:forall j:'I_n,(m<=j)%N ->forall x,
    analytic_representative_value (f j) x = (omega j x)^+(degree j)+
      \sum_(i<degree j) analytic_representative_value ((@b j i))
        (@AnalyticPrefixCoordinates.projection R X n omega (j:nat)
          (leq_trans (leqnSn (j:nat)) (ltn_ord j)) x)*(omega j x)^+(i:nat)
}.
End TailLaws.
