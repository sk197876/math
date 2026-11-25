(** Federer (1969), 4.1.7, p. 359:
    the original support-proper map in the
    actual measure domains U and V.
    The two relative support carriers are
    identified by their original points; properness
    is transported, not added as a premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology functions.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormClassZeroTopology InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentSpaces
  CurrentProperSupport ProperMapUP IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProperSupportDomain.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Local Notation UT := (current_domain R v U).
Local Notation VT := (current_domain R n V).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.

(** Source for [current_map_on_domain]: the
    original map U to V as
    a function of the actual measure
    subspaces, supporting Federer 4.1.7,
    p. 359. This alias changes no values. *)
Definition current_map_on_domain:UT->VT:=
  fun x=>exist _ (f (set_val x)) (mem_set (hImage (set_val x) (set_valP x))).

(** Source for [current_map_on_domain_continuous]:
    class-zero regularity gives continuity between
    the actual original domains, supporting
    Federer 4.1.7, p. 359. *)
Lemma current_map_on_domain_continuous:
  norm_class_zero NX NY U f->continuous current_map_on_domain.
Proof.
move=>hF;apply:(@set_type_continuous_into YT V UT current_map_on_domain).
exact:(@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U f hF).
Qed.

Variable m:nat.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable T:@current_space R h2 v U hU m.
Local Notation support := (@current_support R h2 v U hU m T).
Local Notation ST := [the topologicalType of set_type (support:set XT)].
Local Notation S := [set x:UT|support (set_val x)].
Local Notation SS := [the topologicalType of set_type S].
Local Notation fS := (@current_map_on_support R h2 v n m U hU V T f hImage).
Local Notation fSS := (fun x:SS=>current_map_on_domain (set_val x)).

(** Source for [current_domain_proper_on_support]:
    original properness on spt T is
    precisely sufficient on its copy inside
    the original measure domain U, supporting
    the Radon image in Federer 4.1.7,
    p. 359. No ambient properness is used. *)
Theorem current_domain_proper_on_support:
  @is_current_proper_on_support R h2 v n m U hU V T f hImage->is_proper_map fSS.
Proof.
move=>hp K hK.
pose j:ST->SS:=fun x=>exist _
  (exist _ (set_val x) (mem_set (set_valP x).1)) (mem_set (set_valP x)).
have hJ:continuous j.
  apply:(@set_type_continuous_into UT S ST j).
  apply:(@set_type_continuous_into XT U ST (fun x=>set_val (j x))).
  exact:(@set_type_val_continuous XT support).
have hCompact:compact (j @` (fS @^-1` K)).
  apply:continuous_compact (hp K hK);exact:continuous_subspaceT hJ.
have hEqual:j @` (fS @^-1` K)=fSS @^-1` K.
  apply/seteqP;split.
  - move=>z [x hx <-].
    have hSame:fSS (j x)=fS x by apply:val_inj;by [].
    change (K (fSS (j x))).
    exact:(eq_ind (fS x) K hx (fSS (j x)) (esym hSame)).
  - move=>z hz.
    pose x:ST:=exist _ (set_val (set_val z)) (mem_set (set_valP z)).
    exists x.
    + have hSame:fS x=fSS z by apply:val_inj;by [].
      change (K (fS x)).
      exact:(eq_ind (fSS z) K hz (fS x) (esym hSame)).
    + apply:val_inj;apply:val_inj;by [].
by rewrite hEqual in hCompact.
Qed.
(** Source for [current_domain_support_proper_reverse]:
    properness on the same support inside
    the measure domain implies original support
    properness, supporting the composition formula
    in Federer 4.1.7, p. 359. Only
    the two identical relative support carriers
    are changed. *)
Theorem current_domain_support_proper_reverse:
  is_proper_map fSS->@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Proof.
move=>hp K hK.
pose i:SS->ST:=fun x=>exist _ (set_val (set_val x)) (mem_set (set_valP x)).
have hI:continuous i.
  apply:(@set_type_continuous_into XT support SS i).
  move=>x;exact:(continuous_comp (@set_type_val_continuous UT S x)
    (@set_type_val_continuous XT U (set_val x))).
have hCompact:compact (i @` (fSS @^-1` K)).
  apply:continuous_compact (hp K hK);exact:continuous_subspaceT hI.
have hEqual:i @` (fSS @^-1` K)=fS @^-1` K.
  apply/seteqP;split.
  - move=>z [x hx <-].
    have hSame:fS (i x)=fSS x by apply:val_inj;by [].
    change (K (fS (i x))).
    exact:(eq_ind (fSS x) K hx (fS (i x)) (esym hSame)).
  - move=>z hz.
    pose x:SS:=exist _ (exist _ (set_val z) (mem_set (set_valP z).1)) (mem_set (set_valP z)).
    exists x.
    + have hSame:fSS x=fS z by apply:val_inj;by [].
      change (K (fSS x)).
      exact:(eq_ind (fS z) K hz (fSS x) (esym hSame)).
    + apply:val_inj;by [].
by rewrite hEqual in hCompact.
Qed.
End CurrentProperSupportDomain.
