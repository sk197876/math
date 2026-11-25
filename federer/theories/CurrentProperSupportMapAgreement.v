(** Federer (1969), 4.1.9, p. 363: the endpoint
    maps agree with the homotopy slices on U.
    The support-proper restriction from 4.1.7,
    p. 359, depends only on those original values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentProperSupport ProperMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentProperSupportMapAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Variable T:@current_space R h2 n U hU m.
Variables f g:R_n R n->R_n R nu.
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall x,U x->V (g x).

(** Source for [current_proper_support_map_agreement]: equal
    maps on U have the same properness on spt T,
    supporting the original endpoint identifications
    in Federer 4.1.9, p. 363. Equality outside
    U and a representation of T are unnecessary. *)
Theorem current_proper_support_map_agreement:
  (forall x,U x->f x=g x)->
  @is_current_proper_on_support R h2 n nu m U hU V T f hFImage->
  @is_current_proper_on_support R h2 n nu m U hU V T g hGImage.
Proof.
move=>hFG hProper.
have hEqual:@current_map_on_support R h2 n nu m U hU V T f hFImage=
    @current_map_on_support R h2 n nu m U hU V T g hGImage.
  apply:funext=>x;apply:val_inj.
  exact:(hFG (set_val x) (set_valP x).1).
change (is_proper_map (@current_map_on_support R h2 n nu m U hU V T g hGImage)).
by rewrite -hEqual.
Qed.
End CurrentProperSupportMapAgreement.
